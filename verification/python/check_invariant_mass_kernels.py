#!/usr/bin/env python3
"""Independent exact finite model for Lemma 5.2 (lem:mass-kernels).

The identification of ALL complex invariant forms by Schur's lemma, and the
Zariski-open/dense conclusion, belong to the manuscript proof. This checker
constructs a concrete rational model of the displayed G_SM branching of 3x27.
It checks the finite model using sl(3), sl(2), and q=6Y generators, small local
bilinear-invariance systems (at most 36 unknowns), and actual 81x81 matrices.
There is no import of another verifier, certificate, or manuscript formula as
data, and no solve of the full 81-dimensional invariance system.

Rational ranks agree with complex ranks for these rational matrices. The
generators span the complexified Lie algebra; the connected-group and Schur
interpretations remain mathematical steps in the manuscript. Both doublets
use the natural sl(2) basis, so their cross-pairing is epsilon, and the reverse
block is its TRANSPOSE. Hypercharge forbids a same-charge doublet pairing.

Every rank triple has two explicit witnesses: diagonal multiplicity matrices,
and rationally mixed multiplicity matrices followed by a permutation and
rescaling of all 81 coordinates. Kernel multiplicities are measured from
restricted columns of the full form, independently of the proposed formula.
All checks use explicit exceptions and remain active under python -O.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement, product


class VerificationFailure(RuntimeError):
    """An exact check failed; deliberately independent of Python assertions."""


def require(condition, detail):
    if not condition:
        raise VerificationFailure(detail)


@dataclass
class Matrix:
    nrows: int
    ncols: int
    entries: dict[tuple[int, int], Fraction]


def matrix(nrows, ncols, entries=()):
    out = {}
    for i, j, value in entries:
        require(0 <= i < nrows and 0 <= j < ncols, "matrix index out of bounds")
        require(isinstance(value, (int, Fraction)), "non-exact matrix coefficient")
        out[i, j] = out.get((i, j), Fraction(0)) + Fraction(value)
    return Matrix(nrows, ncols, {key: value for key, value in out.items() if value})


def transpose(a):
    return matrix(a.ncols, a.nrows, ((j, i, v) for (i, j), v in a.entries.items()))


def multiply(a, b):
    require(a.ncols == b.nrows, "matrix product shape")
    rows = {}
    for (i, j), value in b.entries.items():
        rows.setdefault(i, []).append((j, value))
    return matrix(a.nrows, b.ncols, (
        (i, j, av * bv)
        for (i, k), av in a.entries.items() for j, bv in rows.get(k, ())
    ))


def identity(n):
    return matrix(n, n, ((i, i, 1) for i in range(n)))


def echelon(a):
    """Exact sparse row elimination; no block structure or rank formula used."""
    rows = [{} for _ in range(a.nrows)]
    for (i, j), value in a.entries.items():
        rows[i][j] = value
    pivots = {}
    for row in rows:
        while row:
            lead = min(row)
            if lead not in pivots:
                scale = row[lead]
                pivots[lead] = {j: value / scale for j, value in row.items()}
                break
            scale = row[lead]
            for j, value in pivots[lead].items():
                new_value = row.get(j, Fraction(0)) - scale * value
                if new_value:
                    row[j] = new_value
                else:
                    row.pop(j, None)
    return pivots


def rank(a):
    return len(echelon(a))


def nullspace(a):
    pivots = echelon(a)
    basis = []
    for free in range(a.ncols):
        if free in pivots:
            continue
        vector = {free: Fraction(1)}
        for lead in sorted(pivots, reverse=True):
            value = -sum(v * vector.get(j, 0) for j, v in pivots[lead].items()
                         if j != lead)
            if value:
                vector[lead] = value
        basis.append(vector)
    # Certify the returned vectors by multiplication and their free coordinates.
    columns = matrix(a.ncols, len(basis), (
        (i, j, value) for j, vector in enumerate(basis) for i, value in vector.items()
    ))
    require(not multiply(a, columns).entries, "nullspace vector does not vanish")
    require(rank(columns) == len(basis), "dependent nullspace vectors")
    require(len(basis) + len(pivots) == a.ncols, "nullspace dimension")
    return basis


@dataclass(frozen=True, order=True)
class Module:
    colour: int  # 3 = natural, -3 = dual natural, 1 = trivial
    weak: int
    q: int       # integer hypercharge q = 6Y

    @property
    def dim(self):
        return abs(self.colour) * self.weak

    @property
    def dual(self):
        colour = -self.colour if abs(self.colour) == 3 else 1
        return Module(colour, self.weak, -self.q)


Q, UC, EC = Module(3, 2, 1), Module(-3, 1, -4), Module(1, 1, 6)
DC, L = Module(-3, 1, 2), Module(1, 2, -3)
D, H, N = Module(3, 1, -2), Module(1, 2, 3), Module(1, 1, 0)
TYPES = (Q, UC, EC, DC, L, D, H, N)
NAMES = dict(zip(TYPES, ("Q", "uc", "ec", "dc", "L", "D", "H", "1")))
FAMILY = (Q, UC, EC, DC, L)
# Explicit 27 = (10 + bar5 + 1) + (5 + bar5) + 1 under SU(5).
# Listing the two bar5's separately prevents silently losing mirror partners.
BRANCH_27 = (Q, UC, EC, DC, L, N, D, H, DC, L, N)


def chiral_class(multiplicities):
    result = {}
    for rep in sorted(set(multiplicities) | {r.dual for r in multiplicities}):
        if rep < rep.dual:
            value = multiplicities.get(rep, 0) - multiplicities.get(rep.dual, 0)
            if value:
                result[rep] = value
    return result


def check_branching(copies):
    multiplicities = Counter(copies)
    require(sum(rep.dim for rep in copies) == 81, "branching dimension is not 81")
    require(multiplicities == Counter(dict(zip(TYPES, (3, 3, 3, 6, 6, 3, 3, 6)))),
            "branching multiplicities differ from the explicit 3x27 spectrum")
    require(chiral_class(multiplicities) == chiral_class(Counter(FAMILY * 3)),
            "net chiral class differs from three families")
    return multiplicities


def defining_generators(n):
    generators = [(f"E{i}{j}", matrix(n, n, ((i, j, 1),)))
                  for i in range(n) for j in range(n) if i != j]
    generators += [(f"H{i}", matrix(n, n, ((i, i, 1), (i + 1, i + 1, -1))))
                   for i in range(n - 1)]
    return generators


def generators(rep):
    out = {}
    cdim = abs(rep.colour)
    for name, a in defining_generators(3):
        terms = []
        if cdim == 3:
            for (i, j), value in a.entries.items():
                if rep.colour == -3:
                    i, j, value = j, i, -value
                terms.extend((i * rep.weak + w, j * rep.weak + w, value)
                             for w in range(rep.weak))
        out["sl3." + name] = matrix(rep.dim, rep.dim, terms)
    for name, a in defining_generators(2):
        out["sl2." + name] = matrix(rep.dim, rep.dim, (
            (c * rep.weak + i, c * rep.weak + j, value)
            for c in range(cdim) for (i, j), value in a.entries.items()
            if rep.weak == 2
        ))
    out["U1"] = matrix(rep.dim, rep.dim, ((i, i, rep.q) for i in range(rep.dim)))
    return out


def local_pairings(left, right, include_u1=True):
    """Solve A^t B + B C = 0 only on one pair of irreducible summands."""
    rows, terms = 0, []
    ga, gb = generators(left), generators(right)
    for name in ga:
        if name == "U1" and not include_u1:
            continue
        for (k, i), value in ga[name].entries.items():
            terms.extend((rows + i * right.dim + j, k * right.dim + j, value)
                         for j in range(right.dim))
        for (k, j), value in gb[name].entries.items():
            terms.extend((rows + i * right.dim + j, i * right.dim + k, value)
                         for i in range(left.dim))
        rows += left.dim * right.dim
    equations = matrix(rows, left.dim * right.dim, terms)
    return [matrix(left.dim, right.dim, (
        (index // right.dim, index % right.dim, value)
        for index, value in vector.items()
    )) for vector in nullspace(equations)]


def coordinates(copies):
    layout = {rep: [] for rep in TYPES}
    start = 0
    for rep in copies:
        layout[rep].append(tuple(range(start, start + rep.dim)))
        start += rep.dim
    return layout, start


def full_generators(layout, dimension):
    out = {}
    for rep, copies in layout.items():
        for name, a in generators(rep).items():
            out.setdefault(name, []).extend(
                (coords[i], coords[j], value)
                for coords in copies for (i, j), value in a.entries.items()
            )
    return {name: matrix(dimension, dimension, terms) for name, terms in out.items()}


def check_invariant(b, gs, include_u1=True):
    for name, x in gs.items():
        if name == "U1" and not include_u1:
            continue
        left, right = multiply(transpose(x), b), multiply(b, x)
        require(all(left.entries.get(key, 0) + right.entries.get(key, 0) == 0
                    for key in left.entries.keys() | right.entries.keys()),
                f"form fails {name} invariance")


def check_form(b, gs):
    require(b.nrows == b.ncols == 81, "form is not 81x81")
    require(b == transpose(b), "form is not symmetric")
    check_invariant(b, gs)


def insert_pair(terms, left_copies, right_copies, m, pairing):
    for (i, j), value in m.entries.items():
        for (a, b), coefficient in pairing.entries.items():
            row, col = left_copies[i][a], right_copies[j][b]
            terms.extend(((row, col, value * coefficient),
                          (col, row, value * coefficient)))


def build_form(layout, md, ml, s):
    require((md.nrows, md.ncols) == (len(layout[D]), len(layout[DC])),
            "D parameter shape")
    require((ml.nrows, ml.ncols) == (len(layout[H]), len(layout[L])),
            "L parameter shape")
    require(s.nrows == s.ncols == len(layout[N]), "singlet parameter shape")
    require(s == transpose(s), "singlet parameter is not symmetric")
    terms = []
    insert_pair(terms, layout[D], layout[DC], md, identity(3))
    epsilon = matrix(2, 2, ((0, 1, 1), (1, 0, -1)))
    insert_pair(terms, layout[H], layout[L], ml, epsilon)
    terms.extend((layout[N][i][0], layout[N][j][0], value)
                 for (i, j), value in s.entries.items())
    dimension = sum(len(coords) for copies in layout.values() for coords in copies)
    return matrix(dimension, dimension, terms)


def parameter_basis(layout):
    zd, zl, zs = matrix(3, 6), matrix(3, 6), matrix(6, 6)
    basis = []
    for i, j in product(range(len(layout[D])), range(len(layout[DC]))):
        basis.append(build_form(layout, matrix(3, 6, ((i, j, 1),)), zl, zs))
    for i, j in product(range(len(layout[H])), range(len(layout[L]))):
        basis.append(build_form(layout, zd, matrix(3, 6, ((i, j, 1),)), zs))
    for i, j in combinations_with_replacement(range(len(layout[N])), 2):
        terms = [(i, j, 1)] + ([(j, i, 1)] if i != j else [])
        basis.append(build_form(layout, zd, zl, matrix(6, 6, terms)))
    return basis


def check_parameter_basis(basis, gs, dimension):
    require(len(basis) == dimension, "parameter basis cardinality")
    for b in basis:
        check_form(b, gs)
    flattened = matrix(len(basis), 81 * 81, (
        (k, i * 81 + j, value)
        for k, b in enumerate(basis) for (i, j), value in b.entries.items()
    ))
    require(rank(flattened) == dimension, "parameter basis is linearly dependent")


def mixing(n):
    """Explicit invertible rational elementary shears, scales, and reversal."""
    out = matrix(n, n, ((i, n - 1 - i, Fraction((-1) ** i * (i + 2), i + 1))
                        for i in range(n)))
    for i in range(n - 1):
        shear = matrix(n, n, [(j, j, 1) for j in range(n)]
                       + [(i, i + 1, Fraction(i + 1, i + 2))])
        out = multiply(out, shear)
    shear = matrix(n, n, [(j, j, 1) for j in range(n)] + [(n - 1, 0, -2)])
    out = multiply(out, shear)
    require(rank(out) == n, "singular multiplicity basis change")
    return out


def parameters(triple, mixed, p3, p6):
    rd, rl, r0 = triple
    md = matrix(3, 6, ((i, i, i + 1) for i in range(rd)))
    ml = matrix(3, 6, ((i, i, (-1) ** i * (i + 1)) for i in range(rl)))
    s = matrix(6, 6, ((i, i, (-1) ** i * (i + 1)) for i in range(r0)))
    if mixed:
        md = multiply(multiply(transpose(p3), md), p6)
        ml = multiply(multiply(transpose(p3), ml), transpose(p6))
        s = multiply(multiply(transpose(p6), s), p6)
    require((rank(md), rank(ml), rank(s)) == triple, "parameter ranks differ")
    return md, ml, s


def coordinate_change(b, permutation, scales, operator=False):
    # P[old, permutation[old]] = scales[old]. Forms: P^t B P;
    # generators: P^-1 X P. This also checks invariance in the changed basis.
    return matrix(b.nrows, b.ncols, (
        (permutation[i], permutation[j], value *
         (scales[j] / scales[i] if operator else scales[i] * scales[j]))
        for (i, j), value in b.entries.items()
    ))


def measured_kernel(b, layout):
    result = Counter()
    for rep, copies in layout.items():
        columns = [index for coords in copies for index in coords]
        reindex = {old: new for new, old in enumerate(columns)}
        restricted = matrix(b.nrows, len(columns), (
            (i, reindex[j], value) for (i, j), value in b.entries.items() if j in reindex
        ))
        nullity = len(columns) - rank(restricted)
        require(nullity % rep.dim == 0, "kernel not a whole number of modules")
        result[rep] = nullity // rep.dim
    return result


def predicted_kernel(triple):
    rd, rl, r0 = triple
    result = Counter(FAMILY * 3)
    for rep in (D, DC):
        result[rep] += 3 - rd
    for rep in (H, L):
        result[rep] += 3 - rl
    result[N] += 6 - r0
    return result


def check_witness(b, layout, gs, triple):
    check_form(b, gs)
    actual_rank = rank(b)  # Always eliminate the actual full 81x81 matrix first.
    actual_kernel = measured_kernel(b, layout)
    require(actual_kernel == predicted_kernel(triple), "residual module formula")
    actual_nullity = b.ncols - actual_rank
    require(sum(rep.dim * count for rep, count in actual_kernel.items()) == actual_nullity,
            "restricted kernels do not exhaust the full kernel")
    require(chiral_class(actual_kernel) == chiral_class(Counter(FAMILY * 3)),
            "kernel changed the net three-family class")
    rd, rl, r0 = triple
    require(actual_nullity == 81 - 6 * rd - 4 * rl - r0, "kernel dimension formula")
    return actual_rank, actual_nullity


def expect_failure(label, operation, message):
    try:
        operation()
    except VerificationFailure as error:
        require(message in str(error), f"{label}: failed for an unintended reason: {error}")
        return label
    raise VerificationFailure(f"adversarial mutation was accepted: {label}")


def adversarial_checks(copies, layout, gs, basis, parameter_dimension):
    rejected = []

    def reject(label, operation, message):
        rejected.append(expect_failure(label, operation, message))

    # Calibrate exact elimination on cancellation and a tiny nonzero determinant.
    almost = matrix(2, 2, ((0, 0, 1), (0, 1, 1), (1, 0, 1),
                           (1, 1, 1 + Fraction(1, 10 ** 40))))
    require(rank(almost) == 2, "exact elimination lost a tiny rational pivot")
    dependent = matrix(3, 4, ((0, 3, 2), (1, 3, -3), (2, 0, Fraction(2, 3)),
                              (2, 2, Fraction(-4, 3))))
    require(rank(dependent) == 2, "rectangular/proportional-row rank calibration")
    nullspace(dependent)

    for rep in (D, H):
        missing = list(copies)
        missing.remove(rep)
        # Preserve dimension 81 so the detailed multiplicity check must catch it.
        missing.extend([N] * rep.dim)
        reject("missing " + NAMES[rep] + " mirror copy (dimension preserved)",
               lambda missing=missing: check_branching(missing), "multiplicities")

    zd, zl, zs = matrix(3, 6), matrix(3, 6), matrix(6, 6)
    epsilon = matrix(2, 2, ((0, 1, 1), (1, 0, -1)))
    require(local_pairings(L, L) == [], "charged doublet incorrectly self-dual")
    lost_u1 = local_pairings(L, L, include_u1=False)
    require(len(lost_u1) == 1 and rank(lost_u1[0]) == 2,
            "SU(2) epsilon diagnostic dimension/rank")
    require(all(lost_u1[0].entries.get((j, i), 0) == -value
                for (i, j), value in lost_u1[0].entries.items()),
            "SU(2) invariant pairing is not alternating")
    terms = []
    insert_pair(terms, [layout[L][0]], [layout[L][1]], identity(1), epsilon)
    ll = matrix(81, 81, terms)
    require(ll == transpose(ll) and rank(ll) == 4, "doublet self-pair counterexample")
    check_invariant(ll, gs, include_u1=False)
    reject("lost U1 / mistaken weak self-duality", lambda: check_form(ll, gs), "U1")

    terms = []
    insert_pair(terms, [layout[H][0]], [layout[L][0]], identity(1), identity(2))
    wrong_weak = matrix(81, 81, terms)
    reject("identity used instead of weak epsilon", lambda: check_form(wrong_weak, gs), "sl2")

    weak = build_form(layout, zd, matrix(3, 6, ((0, 0, 1),)), zs)
    hcoords = set(layout[H][0])
    wrong_transpose = matrix(81, 81, (
        (i, j, -value if j in hcoords else value) for (i, j), value in weak.entries.items()
    ))
    check_invariant(wrong_transpose, gs)
    reject("wrong weak reverse-block sign", lambda: check_form(wrong_transpose, gs), "symmetric")

    colour = build_form(layout, matrix(3, 6, ((0, 0, 1),)), zl, zs)
    i, j = layout[D][0][0], layout[DC][0][0]
    bad_colour = matrix(81, 81, [(a, b, v) for (a, b), v in colour.entries.items()]
                        + [(i, j, 1), (j, i, 1)])
    reject("one colour component perturbed", lambda: check_form(bad_colour, gs), "sl3")

    reject("rectangular parameter loses a column",
           lambda: build_form(layout, matrix(3, 5), zl, zs), "D parameter shape")
    reject("rectangular parameter transposed",
           lambda: build_form(layout, zd, matrix(6, 3), zs), "L parameter shape")
    reject("singlet parameter loses a copy",
           lambda: build_form(layout, zd, zl, matrix(5, 5)), "singlet parameter shape")
    skew_s = matrix(6, 6, ((0, 1, 1), (1, 0, -1)))
    reject("alternating singlet parameters",
           lambda: build_form(layout, zd, zl, skew_s), "not symmetric")
    a, b = layout[N][0][0], layout[N][1][0]
    skew = matrix(81, 81, ((a, b, 1), (b, a, -1)))
    check_invariant(skew, gs)
    reject("invariant but alternating full form", lambda: check_form(skew, gs), "symmetric")

    reject("missing parameter direction",
           lambda: check_parameter_basis(basis[:-1], gs, parameter_dimension), "cardinality")
    reject("duplicate parameter direction",
           lambda: check_parameter_basis(basis[:-1] + [basis[0]], gs, parameter_dimension),
           "linearly dependent")

    single_mass = build_form(layout, zd, zl, matrix(6, 6, ((0, 0, 1),)))
    require(rank(single_mass) == 1, "singlet rank-one perturbation")
    reject("invariant rank-one perturbation at claimed zero triple",
           lambda: check_witness(single_mass, layout, gs, (0, 0, 0)), "residual module")
    full = build_form(layout, matrix(3, 6, ((i, i, 1) for i in range(3))),
                      matrix(3, 6, ((i, i, 1) for i in range(3))), identity(6))
    missing_pair = build_form(layout, matrix(3, 6, ((i, i, 1) for i in range(2))),
                              matrix(3, 6, ((i, i, 1) for i in range(3))), identity(6))
    require(rank(full) - rank(missing_pair) == 6, "colour-pair rank perturbation")
    reject("deleted massive colour pair at claimed maximal triple",
           lambda: check_witness(missing_pair, layout, gs, (3, 3, 6)), "residual module")
    wrong_residual = measured_kernel(full, layout)
    wrong_residual[DC] -= 3
    reject("residual formula loses the unpaired dc copies",
           lambda: require(wrong_residual == predicted_kernel((3, 3, 6)),
                           "residual module formula"), "residual module")
    reject("rank oracle accepts a false claimed rank",
           lambda: require(rank(almost) == 1, "exact rank mismatch"), "exact rank")
    return rejected


def main():
    require(sum(rep.dim for rep in BRANCH_27) == 27, "one-27 branching dimension")
    copies = BRANCH_27 * 3
    multiplicities = check_branching(copies)
    require(sum(rep.dim for rep in FAMILY) == 15, "minimal-family dimension")
    require(all((rep.q + 2 * (1 if rep.colour == 3 else -1 if rep.colour == -3 else 0)
                 + 3 * (rep.weak - 1)) % 6 == 0 for rep in TYPES), "G_SM charge lattice")
    layout, dimension = coordinates(copies)
    require(dimension == 81, "explicit coordinate count")
    gs = full_generators(layout, dimension)
    require(len(gs) == 12, "complexified gauge-algebra generator count")

    # A finite completeness calculation per species pair, independent of the
    # hand-built I3/epsilon blocks. This is not a full dense invariance solve.
    local_dimensions = {}
    parameter_dimension = 0
    largest_system = 0
    for left, right in combinations_with_replacement(TYPES, 2):
        pairings = local_pairings(left, right)
        largest_system = max(largest_system, left.dim * right.dim)
        require(len(pairings) == int(left.dual == right), "local pairing/duality mismatch")
        if pairings:
            local_dimensions[NAMES[left] + "/" + NAMES[right]] = len(pairings)
            if left == right:
                require(pairings[0] == transpose(pairings[0]), "self-pairing symmetry")
                count = multiplicities[left]
                parameter_dimension += count * (count + 1) // 2
            else:
                parameter_dimension += multiplicities[left] * multiplicities[right]
    require(local_dimensions == {"dc/D": 1, "L/H": 1, "1/1": 1}, "allowed local blocks")
    basis = parameter_basis(layout)
    check_parameter_basis(basis, gs, parameter_dimension)
    require(parameter_dimension == 57, "parameter dimension is not 57")

    permutation = [(17 * i + 11) % dimension for i in range(dimension)]
    scales = [Fraction((-1) ** i * (i % 5 + 1), i % 3 + 1) for i in range(dimension)]
    require(sorted(permutation) == list(range(dimension)) and all(scales),
            "invalid coordinate basis change")
    moved_layout = {rep: [tuple(permutation[i] for i in coords) for coords in rep_copies]
                    for rep, rep_copies in layout.items()}
    moved_gs = {name: coordinate_change(x, permutation, scales, operator=True)
                for name, x in gs.items()}
    p3, p6 = mixing(3), mixing(6)
    results = {}
    mixed_changed = 0
    rank_limits = (min(len(layout[D]), len(layout[DC])),
                   min(len(layout[H]), len(layout[L])), len(layout[N]))
    for triple in product(*(range(limit + 1) for limit in rank_limits)):
        original = None
        for mixed in (False, True):
            md, ml, s = parameters(triple, mixed, p3, p6)
            b = build_form(layout, md, ml, s)
            if mixed:
                require(original is not None, "missing first witness")
                mixed_changed += b != original
                b = coordinate_change(b, permutation, scales)
                observed = check_witness(b, moved_layout, moved_gs, triple)
                require(observed == results[triple], "basis change altered rank/nullity")
            else:
                original = b
                results[triple] = check_witness(b, layout, gs, triple)
    require(len(results) == 112, "rank triples are not exhaustive")
    require(mixed_changed == len(results) - 1, "mixing failed to change a nonzero witness")
    require(min(nullity for _, nullity in results.values()) == 45, "minimum kernel dimension")
    require(max(mass_rank for mass_rank, _ in results.values()) == 36, "maximum mass rank")
    require([triple for triple, (_, nullity) in results.items() if nullity == 45] == [(3, 3, 6)],
            "minimum is not unique to the maximal triple")
    require(predicted_kernel((3, 3, 6)) == Counter(FAMILY * 3), "minimum kernel module")
    rejected = adversarial_checks(copies, layout, gs, basis, parameter_dimension)

    print("Independent invariant-mass-kernel checks passed (Lemma 5.2; lem:mass-kernels)")
    print("Scope: concrete finite rational model; ranks are also exact over C.")
    print("Schur identification of all complex forms and Zariski-open/dense locus: manuscript proof.")
    print("Branching q=6Y: " + ", ".join(
        f"{multiplicities[rep]}{' singlets' if rep == N else NAMES[rep]}"
        f"({'bar3' if rep.colour == -3 else rep.colour},{rep.weak})q{rep.q}"
        for rep in TYPES))
    print("Derived dimensions: one 27 = 27; 3x27 = 81; one minimal family = 15.")
    print("Net chiral class: 3 families; unpaired Q,uc,ec and dc-D=L-H=3.")
    print(f"Local invariance: 36 species pairs; 12 generators; at most {largest_system} unknowns.")
    print("Nonzero local pairing spaces: dc/D=1, L/H=1, 1/1=1; charged self-doublet=0.")
    print(f"Invariant symmetric parameter basis: 18+18+21={parameter_dimension}; full-matrix independence checked.")
    print("r0 runs 0..6 in every row; entries below are measured full-matrix ranks/nullities.")
    for rd, rl in product(range(4), repeat=2):
        masses = ",".join(str(results[rd, rl, r0][0]) for r0 in range(7))
        kernels = ",".join(str(results[rd, rl, r0][1]) for r0 in range(7))
        print(f"rD={rd}, rL={rl}: mass=[{masses}]; kernel=[{kernels}]")
    print("112 triples x 2 witnesses = 224 explicit 81x81 rank/invariance checks.")
    print("Basis stress: rational multiplicity mixing, full coordinate permutation and rational rescaling.")
    print("Residual multiplicities measured separately from all 8 full-matrix column restrictions.")
    print("Residual: 3F + (3-rD)(D+dc) + (3-rL)(H+L) + (6-r0)1; net class always 3F.")
    print("Kernel formula is up to K-module isomorphism; it specifies no preferred subspace or physical mass scale.")
    print("Kernel dimension = 81-6rD-4rL-r0; minimum 45 and maximum mass rank 36 only at (3,3,6).")
    print("Exact rank calibration: rational cancellation, rectangular rows, and a 1/10^40 pivot.")
    for label in rejected:
        print("REJECTED: " + label)
    print(f"PASS: {len(rejected)} adversarial mutations rejected; explicit raises remain active under python -O.")


if __name__ == "__main__":
    main()
