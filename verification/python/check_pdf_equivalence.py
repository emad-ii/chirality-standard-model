#!/usr/bin/env python3
"""Compare searchable, structural, and rendered PDF content across TeX builds."""

from __future__ import annotations

import argparse
import base64
from collections import Counter
from collections.abc import Callable
from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unicodedata
import zlib

from verification_checks import require


# ``/OpenAction`` itself may hold a passive local ``/GoTo`` destination (as
# hyperref emits for the initial page view). Forms and executable, external,
# stateful, media, or attachment action subtypes are rejected below instead.
FORBIDDEN_ACTIVE_NAMES = frozenset(
    {
        b"AA",
        b"AcroForm",
        b"EmbeddedFile",
        b"FileAttachment",
        b"GoTo3DView",
        b"GoToE",
        b"GoToR",
        b"Hide",
        b"ImportData",
        b"JS",
        b"JavaScript",
        b"Launch",
        b"Movie",
        b"Named",
        b"ResetForm",
        b"Rendition",
        b"RichMediaExecute",
        b"RichMedia",
        b"SetOCGState",
        b"Sound",
        b"SubmitForm",
        b"Thread",
        b"Trans",
        b"URI",
        b"Widget",
        b"XFA",
    }
)

PDF_WHITESPACE = frozenset(b"\x00\x09\x0a\x0c\x0d\x20")
PDF_DELIMITERS = frozenset(b"()<>[]{}/%")
MAX_OBJECT_STREAM_BYTES = 64 * 1024 * 1024
MAX_PDF_CONTAINER_DEPTH = 128
FORBIDDEN_FILE_SPECIFICATION_KEYS = frozenset({b"AF", b"EF"})
POSTSCRIPT_SUBTYPE_KEYS = frozenset({b"Subtype", b"Subtype2"})


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment["LC_ALL"] = "C"
    environment["LANG"] = "C"
    result = subprocess.run(
        command,
        check=False,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    require(result.returncode == 0, (command, result.stderr))
    return result


def _is_pdf_separator(value: int) -> bool:
    return value in PDF_WHITESPACE or value in PDF_DELIMITERS


def _decode_pdf_name(raw: bytes) -> bytes:
    """Decode ``#xx`` escapes in a PDF name object."""

    decoded = bytearray()
    index = 0
    while index < len(raw):
        if index + 2 < len(raw) and raw[index] == ord("#"):
            escaped = raw[index + 1 : index + 3]
            if re.fullmatch(rb"[0-9A-Fa-f]{2}", escaped):
                decoded.append(int(escaped, 16))
                index += 3
                continue
        decoded.append(raw[index])
        index += 1
    return bytes(decoded)


def _skip_pdf_literal_string(data: bytes, start: int, context: str) -> int:
    depth = 1
    index = start + 1
    while index < len(data):
        value = data[index]
        if value == ord("\\"):
            index += 1
            if index < len(data) and data[index] == ord("\r"):
                index += 1
                if index < len(data) and data[index] == ord("\n"):
                    index += 1
            elif index < len(data):
                index += 1
            continue
        if value == ord("("):
            depth += 1
        elif value == ord(")"):
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    require(False, f"unterminated PDF literal string in {context}")
    return len(data)


def _stream_dictionary(
    tokens: list[tuple[str, bytes]], context: str
) -> list[tuple[str, bytes]]:
    require(
        tokens and tokens[-1] == ("delimiter", b">>"),
        f"stream without an immediately preceding dictionary in {context}",
    )
    depth = 0
    for index in range(len(tokens) - 1, -1, -1):
        token = tokens[index]
        if token == ("delimiter", b">>"):
            depth += 1
        elif token == ("delimiter", b"<<"):
            depth -= 1
            if depth == 0:
                return tokens[index:]
    require(False, f"unbalanced stream dictionary in {context}")
    return []


def _direct_dictionary_integer(
    tokens: list[tuple[str, bytes]], key: bytes
) -> int | None:
    for index in _top_level_dictionary_name_positions(tokens, key):
        if index + 1 < len(tokens):
            kind, value = tokens[index + 1]
            if kind == "word" and value.isdigit():
                # An indirect reference has the lexical form ``n 0 R``.  Its
                # first token must never be treated as a direct integer: doing
                # so would truncate or overrun the stream before the scanner
                # reaches the real ``endstream`` marker.
                if (
                    index + 3 < len(tokens)
                    and tokens[index + 2][0] == "word"
                    and tokens[index + 2][1].isdigit()
                    and tokens[index + 3] == ("word", b"R")
                ):
                    return None
                return int(value)
            return None
    return None


def _object_stream_bodies(
    decoded: bytes,
    dictionary: list[tuple[str, bytes]],
    context: str,
) -> list[tuple[int, bytes]]:
    """Split a decoded object stream at its declared compressed-object offsets.

    Each compressed object is a separate lexical unit.  Scanning the whole
    decoded payload as one byte string would let a comment at the end of one
    object hide names at the beginning of the next object.
    """

    count = _direct_dictionary_integer(dictionary, b"N")
    first = _direct_dictionary_integer(dictionary, b"First")
    require(
        count is not None and count > 0,
        f"invalid object-stream N in {context}",
    )
    require(
        first is not None and 0 <= first <= len(decoded),
        f"invalid object-stream First in {context}",
    )
    if count is None or first is None:  # Narrow types after fail-closed checks.
        return []

    header = decoded[:first].strip(b"\x00\x09\x0a\x0c\x0d\x20")
    header_words = (
        re.split(rb"[\x00\x09\x0a\x0c\x0d\x20]+", header) if header else []
    )
    require(
        len(header_words) == 2 * count
        and all(word.isdigit() for word in header_words),
        f"invalid object-stream index in {context}",
    )
    if len(header_words) != 2 * count:
        return []

    object_numbers = [
        int(header_words[index]) for index in range(0, len(header_words), 2)
    ]
    offsets = [int(header_words[index]) for index in range(1, len(header_words), 2)]
    payload_size = len(decoded) - first
    require(
        all(number > 0 for number in object_numbers)
        and len(set(object_numbers)) == count,
        f"invalid object numbers in object-stream index in {context}",
    )
    require(
        offsets[0] == 0
        and all(left < right for left, right in zip(offsets, offsets[1:]))
        and offsets[-1] < payload_size,
        f"invalid offsets in object-stream index in {context}",
    )

    boundaries = offsets[1:] + [payload_size]
    return [
        (object_number, decoded[first + start : first + stop])
        for object_number, start, stop in zip(object_numbers, offsets, boundaries)
    ]


def _dictionary_name_value(
    tokens: list[tuple[str, bytes]], key: bytes
) -> bytes | None:
    positions = _top_level_dictionary_name_positions(tokens, key)
    for index in positions:
        require(index + 1 < len(tokens), f"missing /{key.decode('latin-1')} value")
        require(
            tokens[index + 1][0] == "name",
            f"non-name /{key.decode('latin-1')} value cannot be safety-classified",
        )
        return tokens[index + 1][1]
    return None


def _top_level_dictionary_name_positions(
    tokens: list[tuple[str, bytes]], key: bytes
) -> list[int]:
    require(
        tokens
        and tokens[0] == ("delimiter", b"<<")
        and tokens[-1] == ("delimiter", b">>"),
        "invalid top-level PDF dictionary token span",
    )
    return [
        key_index
        for depth, entry_key, key_index, _ in _pdf_dictionary_entries(
            tokens,
            "PDF dictionary",
        )
        if depth == 1 and entry_key == key
    ]


def _is_indirect_reference(
    tokens: list[tuple[str, bytes]], index: int
) -> bool:
    return (
        index + 2 < len(tokens)
        and tokens[index][0] == "word"
        and tokens[index][1].isdigit()
        and tokens[index + 1][0] == "word"
        and tokens[index + 1][1].isdigit()
        and tokens[index + 2] == ("word", b"R")
    )


def _pdf_dictionary_entries(
    tokens: list[tuple[str, bytes]], context: str
) -> list[tuple[int, bytes, int, int]]:
    """Return ``(depth, key, key-index, value-index)`` for all dictionaries."""

    entries: list[tuple[int, bytes, int, int]] = []

    def parse_sequence(index: int, closing: bytes, depth: int) -> int:
        require(
            depth <= MAX_PDF_CONTAINER_DEPTH,
            f"PDF container nesting exceeds {MAX_PDF_CONTAINER_DEPTH} in {context}",
        )
        while index < len(tokens):
            if tokens[index] == ("delimiter", closing):
                return index + 1
            require(
                tokens[index]
                not in {("delimiter", b">>"), ("delimiter", b"]"), ("delimiter", b"}")},
                f"mismatched PDF container in {context}",
            )
            index = parse_value(index, depth)
        require(False, f"unterminated PDF container in {context}")
        return len(tokens)

    def parse_dictionary(index: int, depth: int) -> int:
        require(
            depth <= MAX_PDF_CONTAINER_DEPTH,
            f"PDF dictionary nesting exceeds {MAX_PDF_CONTAINER_DEPTH} in {context}",
        )
        index += 1
        seen_keys: set[bytes] = set()
        while index < len(tokens):
            if tokens[index] == ("delimiter", b">>"):
                return index + 1
            kind, key = tokens[index]
            require(kind == "name", f"non-name PDF dictionary key in {context}")
            require(
                key not in seen_keys,
                f"duplicate /{key.decode('latin-1')} dictionary key in {context}",
            )
            seen_keys.add(key)
            key_index = index
            index += 1
            require(
                index < len(tokens),
                f"missing /{key.decode('latin-1')} dictionary value in {context}",
            )
            entries.append((depth, key, key_index, index))
            index = parse_value(index, depth)
        require(False, f"unterminated PDF dictionary in {context}")
        return len(tokens)

    def parse_value(index: int, depth: int) -> int:
        require(index < len(tokens), f"missing PDF value in {context}")
        token = tokens[index]
        if token == ("delimiter", b"<<"):
            return parse_dictionary(index, depth + 1)
        if token == ("delimiter", b"["):
            return parse_sequence(index + 1, b"]", depth + 1)
        if token == ("delimiter", b"{"):
            return parse_sequence(index + 1, b"}", depth + 1)
        require(
            token[0] != "delimiter",
            f"unexpected PDF delimiter {token[1]!r} in {context}",
        )
        return index + 3 if _is_indirect_reference(tokens, index) else index + 1

    index = 0
    while index < len(tokens):
        if tokens[index] == ("delimiter", b"<<"):
            index = parse_dictionary(index, 1)
        else:
            index += 1
    return entries


def _structural_active_features(
    tokens: list[tuple[str, bytes]], context: str
) -> set[str]:
    """Find security-sensitive dictionary entries in one PDF object.

    This deliberately parses only the bounded token list already produced by
    the lexical scanner.  Strings and stream payloads are represented as
    opaque scalar tokens, so lookalike text cannot become a dictionary key.
    """

    features: set[str] = set()
    for _, key, _, value_index in _pdf_dictionary_entries(tokens, context):
        value = tokens[value_index]
        value_is_reference = _is_indirect_reference(tokens, value_index)
        if key in FORBIDDEN_FILE_SPECIFICATION_KEYS:
            features.add(f"/{key.decode('ascii')} dictionary entry")
        if key in POSTSCRIPT_SUBTYPE_KEYS:
            require(
                not value_is_reference,
                f"indirect /{key.decode('ascii')} cannot be safety-classified in {context}",
            )
            if value == ("name", b"PS"):
                features.add(f"/{key.decode('ascii')} /PS")
    return features


def _dictionary_filters(
    tokens: list[tuple[str, bytes]], context: str
) -> tuple[bytes, ...]:
    for index in _top_level_dictionary_name_positions(tokens, b"Filter"):
        require(index + 1 < len(tokens), f"missing object-stream Filter value in {context}")
        kind, value = tokens[index + 1]
        if kind == "name":
            return (value,)
        require(
            (kind, value) == ("delimiter", b"["),
            f"unsupported object-stream Filter value in {context}",
        )
        filters = []
        for filter_kind, filter_value in tokens[index + 2 :]:
            if (filter_kind, filter_value) == ("delimiter", b"]"):
                require(filters, f"empty object-stream Filter array in {context}")
                return tuple(filters)
            require(
                filter_kind == "name",
                f"unsupported object-stream Filter array entry in {context}",
            )
            filters.append(filter_value)
        require(False, f"unterminated object-stream Filter array in {context}")
        return ()
    return ()


def _require_supported_decode_parameters(
    tokens: list[tuple[str, bytes]], context: str
) -> None:
    for index in _top_level_dictionary_name_positions(tokens, b"DecodeParms"):
        supported = index + 1 < len(tokens) and tokens[index + 1] == ("word", b"null")
        require(
            supported,
            f"unsupported object-stream DecodeParms in {context}",
        )


def _decode_object_stream(
    payload: bytes,
    filters: tuple[bytes, ...],
    context: str,
) -> bytes:
    decoded = payload
    for filter_name in filters:
        try:
            if filter_name in {b"Fl", b"FlateDecode"}:
                decompressor = zlib.decompressobj()
                inflated = decompressor.decompress(
                    decoded,
                    MAX_OBJECT_STREAM_BYTES + 1,
                )
                require(
                    len(inflated) <= MAX_OBJECT_STREAM_BYTES
                    and not decompressor.unconsumed_tail,
                    f"object stream exceeds {MAX_OBJECT_STREAM_BYTES} bytes in {context}",
                )
                inflated += decompressor.flush(
                    MAX_OBJECT_STREAM_BYTES + 1 - len(inflated)
                )
                require(
                    len(inflated) <= MAX_OBJECT_STREAM_BYTES and decompressor.eof,
                    f"invalid or oversized Flate object stream in {context}",
                )
                decoded = inflated
            elif filter_name in {b"AHx", b"ASCIIHexDecode"}:
                compact = re.sub(rb"\s+", b"", decoded).rstrip(b">")
                if len(compact) % 2:
                    compact += b"0"
                decoded = bytes.fromhex(compact.decode("ascii"))
            elif filter_name in {b"A85", b"ASCII85Decode"}:
                compact = re.sub(rb"\s+", b"", decoded)
                if not compact.startswith(b"<~"):
                    compact = b"<~" + compact
                if not compact.endswith(b"~>"):
                    compact += b"~>"
                decoded = base64.a85decode(compact, adobe=True)
            else:
                require(False, f"unsupported object-stream filter {filter_name!r} in {context}")
        except (ValueError, zlib.error) as error:
            require(False, f"cannot decode object stream in {context}: {error}")
    return decoded


def _stream_payload(
    data: bytes,
    start: int,
    length: int | None,
    context: str,
) -> tuple[bytes, int]:
    if length is not None:
        end = start + length
        require(end <= len(data), f"stream length exceeds file in {context}")
        marker = end
        if data[marker : marker + 2] == b"\r\n":
            marker += 2
        elif data[marker : marker + 1] in {b"\r", b"\n"}:
            marker += 1
        require(
            data[marker : marker + 9] == b"endstream"
            and (
                marker + 9 == len(data)
                or _is_pdf_separator(data[marker + 9])
            ),
            f"stream length does not terminate at endstream in {context}",
        )
        return data[start:end], marker + 9

    match = re.search(
        rb"(?:\r\n|\r|\n)endstream(?=$|[\x00\x09\x0a\x0c\x0d\x20()<>\[\]{}/%])",
        data[start:],
    )
    require(match is not None, f"cannot locate endstream in {context}")
    if match is None:  # Explicit fallback after the fail-closed check above.
        return b"", len(data)
    return data[start : start + match.start()], start + match.end()


def _pdf_syntax_names(
    data: bytes,
    context: str,
    *,
    allow_streams: bool,
    structural_features: set[str] | None = None,
    object_body: bool = False,
) -> set[bytes]:
    """Return real PDF name tokens, excluding strings, comments, and stream data.

    Object streams are decoded and scanned because catalog and action
    dictionaries are commonly stored there by modern TeX engines.
    """

    names: set[bytes] = set()
    if structural_features is None:
        structural_features = set()
    object_tokens: list[tuple[str, bytes]] = []
    in_object = object_body
    index = 0

    while index < len(data):
        value = data[index]
        if value in PDF_WHITESPACE:
            index += 1
            continue
        if value == ord("%"):
            newline = re.search(rb"[\r\n]", data[index + 1 :])
            index = len(data) if newline is None else index + 1 + newline.start()
            continue
        if value == ord("("):
            if in_object:
                object_tokens.append(("scalar", b"string"))
            index = _skip_pdf_literal_string(data, index, context)
            continue
        if value == ord("<") and data[index : index + 2] != b"<<":
            end = data.find(b">", index + 1)
            require(end >= 0, f"unterminated PDF hexadecimal string in {context}")
            if in_object:
                object_tokens.append(("scalar", b"string"))
            index = end + 1
            continue
        if data[index : index + 2] in {b"<<", b">>"}:
            token = ("delimiter", data[index : index + 2])
            if in_object:
                object_tokens.append(token)
            index += 2
            continue
        if value in b"[]{}":
            token = ("delimiter", bytes((value,)))
            if in_object:
                object_tokens.append(token)
            index += 1
            continue
        if value == ord("/"):
            end = index + 1
            while end < len(data) and not _is_pdf_separator(data[end]):
                end += 1
            name = _decode_pdf_name(data[index + 1 : end])
            names.add(name)
            if in_object:
                object_tokens.append(("name", name))
            index = end
            continue

        end = index
        while end < len(data) and not _is_pdf_separator(data[end]):
            end += 1
        word = data[index:end]
        require(word, f"unrecognized PDF syntax byte at offset {index} in {context}")

        if word == b"obj":
            require(not in_object, f"nested obj keyword in {context}")
            in_object = True
            object_tokens = []
        elif word == b"endobj":
            require(in_object, f"endobj outside an indirect object in {context}")
            structural_features.update(
                _structural_active_features(object_tokens, context)
            )
            in_object = False
            object_tokens = []
        elif word == b"stream" and allow_streams:
            dictionary = _stream_dictionary(object_tokens, context)
            structural_features.update(
                _structural_active_features(dictionary, context)
            )
            stream_start = end
            if data[stream_start : stream_start + 2] == b"\r\n":
                stream_start += 2
            elif data[stream_start : stream_start + 1] in {b"\r", b"\n"}:
                stream_start += 1
            else:
                require(False, f"stream keyword is not followed by an end-of-line in {context}")

            payload, index = _stream_payload(
                data,
                stream_start,
                _direct_dictionary_integer(dictionary, b"Length"),
                context,
            )
            if _dictionary_name_value(dictionary, b"Type") == b"ObjStm":
                _require_supported_decode_parameters(dictionary, context)
                decoded = _decode_object_stream(
                    payload,
                    _dictionary_filters(dictionary, context),
                    context,
                )
                for object_number, body in _object_stream_bodies(
                    decoded,
                    dictionary,
                    context,
                ):
                    names.update(
                        _pdf_syntax_names(
                            body,
                            f"compressed object {object_number} in {context}",
                            allow_streams=False,
                            structural_features=structural_features,
                            object_body=True,
                        )
                    )
            continue
        elif in_object:
            object_tokens.append(("word", word))
        index = end

    if in_object:
        structural_features.update(
            _structural_active_features(object_tokens, context)
        )
    return names


def _active_pdf_features(data: bytes, context: str) -> list[str]:
    structural_features: set[str] = set()
    names = _pdf_syntax_names(
        data,
        context,
        allow_streams=True,
        structural_features=structural_features,
    )
    structural_features.update(
        f"/{name.decode('ascii')} name"
        for name in names.intersection(FORBIDDEN_ACTIVE_NAMES)
    )
    return sorted(structural_features)


def active_pdf_features(path: Path) -> list[str]:
    return _active_pdf_features(path.read_bytes(), str(path))


def searchable_fingerprint(path: Path, command: str) -> tuple[Counter[str], ...]:
    """Retain stable prose words and multi-digit numbers on each PDF page.

    Math-font encodings differ across TeX distributions: the same visible sum
    can be extracted as either ``sum`` or ``X``, and large delimiters can emit
    variation selectors. Longer ASCII words and multi-digit numbers are stable
    across those encodings. Their page-local multisets check the searchable
    prose and numerical claims without pretending that PDF glyph maps or
    within-page extraction order are canonical. Visible equations and layout
    are checked independently by rendering.
    """

    raw = run([command, "-enc", "UTF-8", str(path), "-"]).stdout
    raw_pages = raw.split("\f")
    if raw_pages and not raw_pages[-1].strip():
        raw_pages.pop()

    pages = []
    for raw_page in raw_pages:
        normalized = unicodedata.normalize("NFKC", raw_page)
        tokens = [
            token.casefold()
            for token in re.findall(r"[A-Za-z]{4,}|[0-9]{2,}", normalized)
        ]
        pages.append(Counter(tokens))

    require(
        sum(sum(page.values()) for page in pages) >= 1_000,
        f"insufficient searchable text in {path}",
    )
    return tuple(pages)


def fingerprint_delta(
    left: tuple[Counter[str], ...],
    right: tuple[Counter[str], ...],
) -> str:
    if len(left) != len(right):
        return f"page counts differ: {len(left)} != {len(right)}"
    for index, (left_page, right_page) in enumerate(zip(left, right), start=1):
        if left_page != right_page:
            return (
                f"page {index}: left-only={(left_page - right_page).most_common(8)}; "
                f"right-only={(right_page - left_page).most_common(8)}"
            )
    return "unknown fingerprint mismatch"


def pdfinfo_fields(path: Path, command: str) -> dict[str, str]:
    selected = {
        "Title",
        "Subject",
        "Keywords",
        "Author",
        "Pages",
        "Encrypted",
        "Form",
        "JavaScript",
        "Page size",
        "Page rot",
    }
    fields = {}
    for line in run([command, str(path)]).stdout.splitlines():
        key, separator, value = line.partition(":")
        if separator and key in selected:
            fields[key] = value.strip()
    require(fields.keys() == selected, f"missing stable PDF metadata in {path}")
    return fields


def require_no_active_content(
    path: Path,
    pdfinfo_command: str,
    pdfdetach_command: str,
    metadata: dict[str, str],
) -> None:
    """Reject forms, external actions, scripts, attachments, and active media."""

    form_status = metadata.get("Form", "").strip().casefold()
    require(
        form_status == "none",
        f"interactive or XFA form reported in {path}: "
        f"{metadata.get('Form', '<missing>')}",
    )
    javascript_status = metadata.get("JavaScript", "").strip().casefold()
    require(
        javascript_status == "no",
        f"JavaScript metadata reported in {path}: "
        f"{metadata.get('JavaScript', '<missing>')}",
    )

    url_lines = run([pdfinfo_command, "-url", str(path)]).stdout.splitlines()
    external_urls = [
        line.strip() for line in url_lines if re.match(r"^\s*\d+\s+", line)
    ]
    require(not external_urls, f"external URL annotations in {path}: {external_urls[:5]}")

    javascript = run([pdfinfo_command, "-js", str(path)]).stdout.strip()
    require(not javascript, f"document JavaScript in {path}: {javascript[:200]}")

    attachment_lines = [
        line.strip()
        for line in run([pdfdetach_command, "-list", str(path)]).stdout.splitlines()
        if line.strip()
    ]
    require(attachment_lines, f"missing embedded-file inventory for {path}")
    count_match = re.match(r"^(\d+)(?:\s|$)", attachment_lines[0])
    require(
        count_match is not None,
        f"unrecognized embedded-file inventory for {path}: {attachment_lines[:5]}",
    )
    attachment_count = -1 if count_match is None else int(count_match.group(1))
    require(
        attachment_count == 0,
        f"{attachment_count} embedded file(s) in {path}: {attachment_lines[1:6]}",
    )

    active_features = active_pdf_features(path)
    require(
        not active_features,
        f"active PDF structures in {path}: {active_features}",
    )


def require_embedded_fonts(path: Path, command: str) -> int:
    rows = run([command, str(path)]).stdout.splitlines()[2:]
    rows = [row for row in rows if row.strip()]
    require(rows, f"no fonts reported in {path}")
    unembedded = [
        row for row in rows if len(row.split()) < 5 or row.split()[-5] != "yes"
    ]
    require(not unembedded, f"unembedded fonts in {path}: {unembedded[:5]}")
    return len(rows)


def rendered_pages(
    path: Path,
    command: str,
    destination: Path,
    dpi: int,
    *,
    color_mode: str = "rgb",
) -> dict[str, str]:
    """Rasterize every page to deterministic PNG in the selected color mode."""

    require(color_mode in {"rgb", "gray"}, f"unsupported render mode: {color_mode}")

    prefix = destination / "page"
    color_arguments = [] if color_mode == "rgb" else ["-gray"]
    run(
        [
            command,
            "-r",
            str(dpi),
            *color_arguments,
            "-png",
            "-aa",
            "no",
            "-aaVector",
            "no",
            str(path),
            str(prefix),
        ]
    )
    pages = sorted(destination.glob("page-*.png"))
    require(pages, f"no pages rendered from {path}")
    return {page.name: sha256(page.read_bytes()).hexdigest() for page in pages}


def require_matching_renders(
    left_pages: dict[str, str],
    right_pages: dict[str, str],
    *,
    dpi: int,
    color_mode: str,
) -> None:
    require(
        left_pages.keys() == right_pages.keys(),
        f"{color_mode.upper()} rendered page sets differ: "
        f"{left_pages.keys()} != {right_pages.keys()}",
    )
    differing = [
        name for name in left_pages if left_pages[name] != right_pages[name]
    ]
    render_delta = ", ".join(
        f"{name} ({left_pages[name][:12]} != {right_pages[name][:12]})"
        for name in differing[:8]
    )
    require(
        not differing,
        f"{color_mode.upper()} rendered pages differ at {dpi} dpi: {render_delta}",
    )


def _synthetic_object_stream(objects: list[bytes]) -> bytes:
    require(objects and all(objects), "synthetic object stream needs nonempty objects")
    offsets: list[int] = []
    bodies = bytearray()
    for body in objects:
        offsets.append(len(bodies))
        bodies.extend(body)
        bodies.extend(b"\n")
    header = b"".join(
        f"{object_number} {offset} ".encode("ascii")
        for object_number, offset in enumerate(offsets, start=10)
    )
    decoded = header + bodies
    compressed = zlib.compress(decoded)
    dictionary = (
        f"<< /Type /ObjStm /N {len(objects)} /First {len(header)} "
        f"/Length {len(compressed)} /Filter /FlateDecode >>"
    ).encode("ascii")
    return (
        b"%PDF-1.7\n1 0 obj\n"
        + dictionary
        + b"\nstream\n"
        + compressed
        + b"\nendstream\nendobj\n%%EOF\n"
    )


def _synthetic_color_pdf(red: str, green: str, blue: str) -> bytes:
    content = (
        f"{red} {green} {blue} rg\n0 0 16 16 re f\n"
    ).encode("ascii")
    objects = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        (
            b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 16 16] "
            b"/Resources << >> /Contents 4 0 R >>"
        ),
        (
            f"<< /Length {len(content)} >>\nstream\n".encode("ascii")
            + content
            + b"endstream"
        ),
    ]
    pdf = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
    offsets = [0]
    for object_number, body in enumerate(objects, start=1):
        offsets.append(len(pdf))
        pdf.extend(f"{object_number} 0 obj\n".encode("ascii"))
        pdf.extend(body)
        pdf.extend(b"\nendobj\n")
    xref_offset = len(pdf)
    pdf.extend(f"xref\n0 {len(objects) + 1}\n".encode("ascii"))
    pdf.extend(b"0000000000 65535 f \n")
    for offset in offsets[1:]:
        pdf.extend(f"{offset:010d} 00000 n \n".encode("ascii"))
    pdf.extend(
        (
            f"trailer\n<< /Size {len(objects) + 1} /Root 1 0 R >>\n"
            f"startxref\n{xref_offset}\n%%EOF\n"
        ).encode("ascii")
    )
    return bytes(pdf)


def _expect_verification_failure(
    operation: Callable[[], object], label: str
) -> str:
    try:
        operation()
    except RuntimeError as error:
        return str(error)
    require(False, f"self-test unexpectedly accepted {label}")
    return ""


def run_self_tests(pdftoppm_command: str) -> None:
    direct_probe = (
        b"%PDF-1.7\n"
        b"1 0 obj\n<< /Type /Catalog /A#46 [2 0 R] >>\nendobj\n"
        b"2 0 obj\n<< /Type /Filespec /E#46 << /F 3 0 R >> >>\nendobj\n"
        b"3 0 obj\n<< /Type /XObject /Subtype /P#53 /Length 0 >>\n"
        b"stream\nendstream\nendobj\n"
        b"4 0 obj\n<< /Type /XObject /Subtype2 /PS >>\nendobj\n%%EOF\n"
    )
    required_features = {
        "/AF dictionary entry",
        "/EF dictionary entry",
        "/Subtype /PS",
        "/Subtype2 /PS",
    }
    direct_features = set(_active_pdf_features(direct_probe, "direct self-test"))
    require(
        required_features <= direct_features,
        f"direct structural self-test missed {required_features - direct_features}",
    )

    compressed_probe = _synthetic_object_stream(
        [
            b"<< /Type /Catalog /AF [11 0 R] >>",
            b"<< /Type /Filespec /EF << /F 12 0 R >> >>",
            b"<< /Type /XObject /Subtype /PS >>",
            b"<< /Type /XObject /Subtype2 /PS >>",
        ]
    )
    compressed_probe = compressed_probe.replace(
        b"<< /Type /ObjStm",
        b"<< /Alias /Type /Type /ObjStm",
        1,
    )
    compressed_features = set(
        _active_pdf_features(compressed_probe, "compressed self-test")
    )
    require(
        required_features <= compressed_features,
        f"compressed structural self-test missed "
        f"{required_features - compressed_features}",
    )

    indirect_type_probe = _synthetic_object_stream([b"<< /Safe true >>"]).replace(
        b"/Type /ObjStm",
        b"/Type 99 0 R",
        1,
    )
    _expect_verification_failure(
        lambda: _active_pdf_features(indirect_type_probe, "indirect-type self-test"),
        "an indirect object-stream Type",
    )
    indirect_filter_probe = _synthetic_object_stream([b"<< /Safe true >>"]).replace(
        b"/Filter /FlateDecode",
        b"/Filter [/FlateDecode 99 0 R]",
        1,
    )
    _expect_verification_failure(
        lambda: _active_pdf_features(
            indirect_filter_probe,
            "indirect-filter self-test",
        ),
        "an unclassifiable object-stream filter",
    )

    decoy_probe = (
        b"%PDF-1.7\n1 0 obj\n"
        b"<< /Note (/AF /EF /Subtype /PS) /Alias /AF /Kind /PS "
        b"/Subtype /Image >>\nendobj\n%%EOF\n"
    )
    require(
        not _active_pdf_features(decoy_probe, "decoy self-test"),
        "dictionary-value or string decoy was treated as active content",
    )

    malformed_probe = b"%PDF-1.7\n1 0 obj\n<< /EF >>\nendobj\n%%EOF\n"
    _expect_verification_failure(
        lambda: _active_pdf_features(malformed_probe, "malformed self-test"),
        "a missing sensitive dictionary value",
    )

    with tempfile.TemporaryDirectory(prefix="pdf-equivalence-self-test-") as tmp:
        root = Path(tmp)
        black = root / "black.pdf"
        near_black_blue = root / "near-black-blue.pdf"
        black.write_bytes(_synthetic_color_pdf("0", "0", "0"))
        near_black_blue.write_bytes(
            _synthetic_color_pdf("0", "0", "0.003921568627451")
        )

        gray_left_dir = root / "gray-left"
        gray_right_dir = root / "gray-right"
        rgb_left_dir = root / "rgb-left"
        rgb_right_dir = root / "rgb-right"
        for directory in (
            gray_left_dir,
            gray_right_dir,
            rgb_left_dir,
            rgb_right_dir,
        ):
            directory.mkdir()

        gray_left = rendered_pages(
            black,
            pdftoppm_command,
            gray_left_dir,
            72,
            color_mode="gray",
        )
        gray_right = rendered_pages(
            near_black_blue,
            pdftoppm_command,
            gray_right_dir,
            72,
            color_mode="gray",
        )
        require(
            gray_left == gray_right,
            "synthetic color pair is not a grayscale collision on this renderer",
        )

        rgb_left = rendered_pages(
            black,
            pdftoppm_command,
            rgb_left_dir,
            72,
            color_mode="rgb",
        )
        rgb_right = rendered_pages(
            near_black_blue,
            pdftoppm_command,
            rgb_right_dir,
            72,
            color_mode="rgb",
        )
        diagnostic = _expect_verification_failure(
            lambda: require_matching_renders(
                rgb_left,
                rgb_right,
                dpi=72,
                color_mode="rgb",
            ),
            "distinct RGB renders",
        )
        require(
            "RGB rendered pages differ at 72 dpi" in diagnostic,
            f"unclear RGB mismatch diagnostic: {diagnostic}",
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("left", type=Path, nargs="?")
    parser.add_argument("right", type=Path, nargs="?")
    parser.add_argument("--pdftotext", default="pdftotext")
    parser.add_argument("--pdftoppm", default="pdftoppm")
    parser.add_argument("--pdfinfo", default="pdfinfo")
    parser.add_argument("--pdffonts", default="pdffonts")
    parser.add_argument("--pdfdetach", default="pdfdetach")
    parser.add_argument("--dpi", type=int, default=288)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run bounded parser probes and two tiny one-page render probes",
    )
    args = parser.parse_args()

    if args.self_test:
        if args.left is not None or args.right is not None:
            parser.error("--self-test does not accept PDF operands")
        run_self_tests(args.pdftoppm)
        print("PASS  adversarial PDF parser and RGB-render self-tests")
        return
    if args.left is None or args.right is None:
        parser.error("left and right PDF operands are required")

    require(args.dpi >= 144, "rendering resolution must be at least 144 dpi")
    left_info = pdfinfo_fields(args.left, args.pdfinfo)
    right_info = pdfinfo_fields(args.right, args.pdfinfo)
    require(
        left_info == right_info,
        f"stable PDF metadata differs: {left_info} != {right_info}",
    )
    left_fonts = require_embedded_fonts(args.left, args.pdffonts)
    right_fonts = require_embedded_fonts(args.right, args.pdffonts)
    require_no_active_content(args.left, args.pdfinfo, args.pdfdetach, left_info)
    require_no_active_content(args.right, args.pdfinfo, args.pdfdetach, right_info)

    left_text = searchable_fingerprint(args.left, args.pdftotext)
    right_text = searchable_fingerprint(args.right, args.pdftotext)
    require(
        left_text == right_text,
        "page-local searchable prose/number fingerprints differ: "
        + fingerprint_delta(left_text, right_text),
    )

    with tempfile.TemporaryDirectory(prefix="pdf-equivalence-") as tmp:
        root = Path(tmp)
        left_dir = root / "left"
        right_dir = root / "right"
        left_dir.mkdir()
        right_dir.mkdir()
        left_pages = rendered_pages(args.left, args.pdftoppm, left_dir, args.dpi)
        right_pages = rendered_pages(args.right, args.pdftoppm, right_dir, args.dpi)

    require_matching_renders(
        left_pages,
        right_pages,
        dpi=args.dpi,
        color_mode="rgb",
    )
    print(
        f"PASS  stable metadata, embedded fonts ({left_fonts}/{right_fonts}), "
        f"no active content, page-local searchable fingerprints, and {len(left_pages)} exact "
        f"{args.dpi}-dpi RGB renders"
    )


if __name__ == "__main__":
    main()
