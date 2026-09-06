import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import {
  candidates,
  cells,
  checkCertificate,
  edges,
  inspectCell,
  points,
  reflections,
  roots,
  spacePoints,
} from '../lib/e6.ts';

const expected = [
  { profile: [16, 10, 6], common: 2, dimensions: [21, 14, 9] },
  { profile: [16, 10, 6], common: 6, dimensions: [21, 14, 9] },
  { profile: [16, 10, 14], common: 6, dimensions: [21, 14, 19] },
  { profile: [16, 10, 14], common: 10, dimensions: [21, 14, 19] },
  { profile: [20, 10, 6], common: 4, dimensions: [24, 14, 9] },
  { profile: [20, 10, 14], common: 8, dimensions: [24, 14, 19] },
];
assert.equal(checkCertificate().passed, true);
assert.equal(points.length, 72);
assert.equal(
  new Set(spacePoints.map((p) => p.map((x) => x.toFixed(6)).join(','))).size,
  72,
);
assert(spacePoints.every((p) => p.every(Number.isFinite)));
assert.equal(edges.length, 720);
assert(points.every((p) => p.every(Number.isFinite)));
// E6's Coxeter projection has coincidences, represented by concentric rings.
const positions = new Map<string, number>();
for (const p of points) {
  const key = p.map((x) => x.toFixed(6)).join(',');
  positions.set(key, (positions.get(key) || 0) + 1);
}
assert.equal(positions.size, 48);
assert.equal([...positions.values()].filter((n) => n === 2).length, 24);
assert.equal([...positions.values()].filter((n) => n === 1).length, 24);

for (let i = 0; i < cells.length; i++) {
  let permutation = roots.map((_, j) => j);
  for (let n = 0; n < 120; n++) {
    const result = inspectCell(i, permutation);
    assert.deepEqual(result.profile, expected[i].profile);
    assert.deepEqual(result.dimensions, expected[i].dimensions);
    assert.equal(result.common.length, expected[i].common);
    permutation = permutation.map((j) => reflections[n % 6][j]);
  }
}
const coxeter = roots.map((_, i) => reflections.reduce((r, p) => p[r], i));
for (let i = 0; i < 72; i++) {
  let r = i;
  for (let n = 0; n < 12; n++) r = coxeter[r];
  assert.equal(r, i);
  const [x, y] = points[i].map((v) => v - 280);
  const [a, b] = points[coxeter[i]].map((v) => v - 280);
  const angle = Math.PI / 6;
  assert(Math.abs(a - (x * Math.cos(angle) + y * Math.sin(angle))) < 1e-6);
  assert(Math.abs(b - (-x * Math.sin(angle) + y * Math.cos(angle))) < 1e-6);
}
assert.throws(() => inspectCell(-1));
assert.throws(() => inspectCell(6));
assert.throws(() => inspectCell(1.5));
assert.deepEqual(
  candidates.map((c) => c.coefficients),
  [[1], [21, -6], [9, 9, 9], [6, -15], [9], [0, 27]],
);
assert.equal(candidates.filter((c) => c.radical !== '0').length, 1);
assert.equal(15 + 10 + 2, 27);
assert.equal(45 + 30 + 6, 81);
assert.equal(
  readFileSync('public/e6-certificate.json', 'utf8'),
  readFileSync('lib/certificate.json', 'utf8'),
);
const notebook = JSON.parse(
  readFileSync('public/Cubic_Anomaly_Master_Verification.ipynb', 'utf8'),
);
assert.equal(notebook.nbformat, 4);
assert(
  notebook.cells.some((c: { cell_type: string }) => c.cell_type === 'code'),
);
console.log(
  'PASS: six local checks; 720 reflected-cell states; Coxeter projection and multiplicities; candidate coefficients; branching arithmetic; certificate identity; notebook structure.',
);
