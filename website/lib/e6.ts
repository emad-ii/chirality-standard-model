import certificate from './certificate.json' with { type: 'json' };

export const snapshot = 'main';
export const repository = 'https://github.com/emad-ii/chirality-standard-model';
export const roots = certificate.roots;
export const cartan = certificate.cartan_matrix;
export const reflections = certificate.simple_reflection_permutations.map((p) =>
  p.map((i) => i - 1),
);
export const cells = certificate.cell_representatives.map((c, index) => ({
  ...c,
  index,
  D: c.D_root_indices.map((i) => i - 1),
  A: c.A_root_indices.map((i) => i - 1),
  T: c.Theta_root_indices.map((i) => i - 1),
}));
export const inner = (a: number[], b: number[]) =>
  a.reduce(
    (sum, x, i) => sum + x * b.reduce((s, y, j) => s + cartan[i][j] * y, 0),
    0,
  );
export const intersect = (...sets: number[][]) =>
  sets[0].filter((i) => sets.slice(1).every((s) => s.includes(i)));
export function rank(indices: number[]) {
  const a = indices.map((i) => [...roots[i]]);
  let r = 0;
  for (let j = 0; j < 6 && r < a.length; j++) {
    const pivot = a.findIndex((row, i) => i >= r && Math.abs(row[j]) > 1e-9);
    if (pivot < 0) continue;
    [a[r], a[pivot]] = [a[pivot], a[r]];
    const divisor = a[r][j];
    a[r] = a[r].map((x) => x / divisor);
    for (let i = 0; i < a.length; i++) {
      if (i === r) continue;
      const factor = a[i][j];
      a[i] = a[i].map((x, k) => x - factor * a[r][k]);
    }
    r++;
  }
  return r;
}

// Fourier projection onto a Coxeter eigenspace (Coxeter number h = 12).
// The root positions are mathematical data, not a drawing of physical particles.
const coxeter = roots.map((_, i) => reflections.reduce((r, p) => p[r], i));
const rawPoints = roots.map((_, i) => {
  let index = i,
    x = 0,
    y = 0;
  for (let k = 0; k < 12; k++) {
    const f = roots[index][0];
    x += f * Math.cos((2 * Math.PI * k) / 12);
    y += f * Math.sin((2 * Math.PI * k) / 12);
    index = coxeter[index];
  }
  return [x, y];
});
const scale = Math.max(...rawPoints.map(([x, y]) => Math.hypot(x, y)));
export const points = rawPoints.map(([x, y]) => [
  (x / scale) * 234 + 280,
  (y / scale) * 234 + 280,
]);
export const edges = roots.flatMap((a, i) =>
  roots.flatMap((b, j) => (j > i && inner(a, b) === 1 ? [[i, j]] : [])),
);

// An independent linear coordinate resolves the Coxeter-plane coincidences.
const rawDepth = roots.map((r) =>
  r.reduce((sum, x, j) => sum + x * Math.sqrt([1, 2, 3, 5, 7, 11][j]), 0),
);
const depthScale = Math.max(...rawDepth.map(Math.abs));
export const spacePoints = roots.map((_, i) => [
  (points[i][0] - 280) / 100,
  (points[i][1] - 280) / 100,
  (rawDepth[i] / depthScale) * 2.2,
]);

export function inspectCell(
  index: number,
  permutation = roots.map((_, i) => i),
) {
  const cell = cells[index];
  if (!cell) throw new Error('Select a cell numbered 1 to 6.');
  const D = cell.D.map((i) => permutation[i]);
  const A = cell.A.map((i) => permutation[i]);
  const T = cell.T.map((i) => permutation[i]);
  const pairs = [intersect(D, A), intersect(D, T), intersect(A, T)];
  const common = intersect(D, A, T);
  return {
    D,
    A,
    T,
    pairs,
    common,
    profile: pairs.map((p) => p.length),
    dimensions: pairs.map((p) => p.length + rank(p)),
  };
}

export function checkCertificate() {
  const checks: { label: string; passed: boolean }[] = [];
  checks.push({
    label: '72 distinct roots, each of squared length 2',
    passed:
      roots.length === 72 &&
      new Set(roots.map((r) => r.join(','))).size === 72 &&
      roots.every((r) => inner(r, r) === 2),
  });
  checks.push({
    label: 'Six simple reflections reconstructed from the Cartan matrix',
    passed: reflections.every(
      (p, k) =>
        new Set(p).size === 72 &&
        roots.every((r, i) => {
          const reflected = [...r];
          reflected[k] -= r.reduce((s, x, j) => s + x * cartan[j][k], 0);
          return (
            reflected.every((x, j) => x === roots[p[i]][j]) && p[p[i]] === i
          );
        }),
    ),
  });
  checks.push({
    label: 'All six representative intersection profiles',
    passed: cells.every((c, i) => {
      const result = inspectCell(i);
      return (
        result.profile.every((n, j) => n === c.profile[j]) &&
        result.common.length === c.common_root_count
      );
    }),
  });
  checks.push({
    label: 'Weyl reflections preserve the six representative profiles',
    passed: cells.every((c, i) =>
      reflections.every((p) => {
        const result = inspectCell(i, p);
        return (
          result.profile.every((n, j) => n === c.profile[j]) &&
          result.common.length === c.common_root_count
        );
      }),
    ),
  });
  checks.push({
    label: 'Published cell counts add to 38,880 = 27 × 36 × 40',
    passed: cells.reduce((s, c) => s + c.cell_count, 0) === 27 * 36 * 40,
  });
  checks.push({
    label: 'D ∩ A has the largest semisimple dimension in every representative',
    passed: cells.every((_, i) => {
      const d = inspectCell(i).dimensions;
      return d[0] > d[1] && d[0] > d[2];
    }),
  });
  return {
    passed: checks.every((c) => c.passed),
    checks,
    scope:
      'Local root and representative checks; the full orbit enumeration and Lean verification are in the downloadable notebook.',
  };
}

export const candidates = [
  {
    g: 'G₂',
    h: 'A₂',
    module: '3',
    dimension: 3,
    coefficients: [1],
    labels: ['A₂'],
    radical: '0',
    detail:
      'The cubic trace on the defining 3 of SU(3) is nonzero. Its simple algebra has no nonzero anomaly-safe ideal.',
  },
  {
    g: 'F₄',
    h: 'A₂ + A₂',
    module: '6 ⊗ 3̄',
    dimension: 18,
    coefficients: [21, -6],
    labels: ['A₂', 'A₂'],
    radical: '0',
    detail:
      'Both simple factors carry nonzero cubic coefficients. Neither can lie in the radical.',
  },
  {
    g: 'E₆',
    h: 'A₂ + A₂ + A₂',
    module: '3 ⊗ 3 ⊗ 3',
    dimension: 27,
    coefficients: [9, 9, 9],
    labels: ['A₂', 'A₂', 'A₂'],
    radical: '0',
    detail:
      'Each SU(3) factor sees nine copies of its defining representation. Every simple factor has a nonzero cubic trace.',
  },
  {
    g: 'E₇',
    h: 'A₅ + A₂',
    module: '15 ⊗ 3̄',
    dimension: 45,
    coefficients: [6, -15],
    labels: ['A₅', 'A₂'],
    radical: '0',
    detail:
      'The two cubic coefficients are nonzero. Opposite signs do not cancel tensors on different simple factors.',
  },
  {
    g: 'E₈',
    h: 'A₈',
    module: 'Λ³ 9',
    dimension: 84,
    coefficients: [9],
    labels: ['A₈'],
    radical: '0',
    detail:
      'The exterior-cube representation of SU(9) has nonzero cubic coefficient. The radical is zero.',
  },
  {
    g: 'E₈',
    h: 'E₆ + A₂',
    module: '27 ⊗ 3',
    dimension: 81,
    coefficients: [0, 27],
    labels: ['E₆', 'A₂'],
    radical: 'E₆',
    detail:
      'The E₆ Lie algebra admits no invariant symmetric cubic tensor. Its factor is in the radical; the SU(3) multiplicity factor has coefficient 27. The anomaly-safe gauge ideal is precisely E₆.',
  },
];
