#!/usr/bin/env python3
"""Runtime checks that remain active under every Python optimization level."""

from __future__ import annotations


class VerificationFailure(RuntimeError):
    """Raised when an exact verification invariant does not hold."""


def require(condition: object, detail: object | None = None) -> None:
    """Require an invariant without relying on Python's removable ``assert``."""
    if condition:
        return
    if detail is None:
        raise VerificationFailure("verification invariant failed")
    raise VerificationFailure(f"verification invariant failed: {detail!r}")
