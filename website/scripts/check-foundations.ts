import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import {
  initialVector,
  radians,
  orderedRotation,
  rotationSeparation,
  phaseVector,
  weakDoublet,
  leptonCharge,
  nextDemoAngle,
} from '../lib/symmetry-lab.ts';
import { resolvePath, chapterForAnchor } from '../lib/reader-paths.ts';

const near = (actual: number, expected: number, tolerance = 1e-12) =>
  assert(Math.abs(actual - expected) <= tolerance, `${actual} != ${expected}`);
near(Math.hypot(...initialVector), 1);
for (let angle = -720; angle <= 720; angle++) {
  for (const order of ['xz', 'zx'] as const)
    near(Math.hypot(...orderedRotation(initialVector, angle, order)), 1);
  for (const charge of [-2, -1, 0, 1, 2])
    near(Math.hypot(...phaseVector(angle, charge)), 1);
  near(Math.hypot(...weakDoublet(angle)), 1);
}
near(rotationSeparation(0), 0);
near(rotationSeparation(90), Math.sqrt(8 / 3));
// The leading commutator rotates the generic initial vector in the x-z plane.
near(rotationSeparation(0.01) / radians(0.01) ** 2, Math.sqrt(2 / 3), 1e-7);
assert(rotationSeparation(30) > 0);
for (const charge of [1, 2]) {
  near(phaseVector(360, charge)[0], 1);
  near(phaseVector(360, charge)[1], 0);
}
near(phaseVector(180, 1)[0], -1);
near(phaseVector(180, 2)[0], 1);
near(weakDoublet(360)[0], -1);
near(weakDoublet(720)[0], 1);
near(weakDoublet(180)[0], 0);
near(weakDoublet(180)[1], 1);
near(leptonCharge(0.5), 0);
near(leptonCharge(-0.5), -1);
for (const angle of [NaN, Infinity, -Infinity]) {
  assert.throws(() => radians(angle));
  assert.throws(() => phaseVector(angle, 1));
  assert.throws(() => weakDoublet(angle));
}
assert.throws(() => phaseVector(0, 0.5));
assert.throws(() => phaseVector(0, Infinity));
for (const [limit, step, selectable] of [
  [90, 15, 1],
  [360, 30, 5],
  [720, 30, 5],
]) {
  for (let angle = 0; angle <= limit; angle += selectable) {
    let n = angle;
    for (let i = 0; i < 200; i++) {
      n = nextDemoAngle(n, step, limit);
      assert(
        n >= 0 && n <= limit,
        `Resumed demo exceeded ${limit}° from ${angle}°`,
      );
    }
  }
}
near(nextDemoAngle(89, 15, 90), 90);
near(nextDemoAngle(715, 30, 720), 720);
for (const args of [
  [-1, 1, 90],
  [91, 1, 90],
  [0, 0, 90],
  [NaN, 1, 90],
  [0, Infinity, 90],
  [0, 1, 0],
])
  assert.throws(() => nextDemoAngle(...(args as [number, number, number])));
const curious = resolvePath('curious').chapters;
assert(curious.indexOf('foundations') < curious.indexOf('physics'));
assert(curious.indexOf('physics') < curious.indexOf('frontiers'));
assert(curious.indexOf('frontiers') < curious.indexOf('selection'));
assert.equal(chapterForAnchor('lie-algebra'), 'foundations');
assert.equal(chapterForAnchor('representations'), 'foundations');
assert.equal(chapterForAnchor('charge-key'), 'physics');
const roots = readFileSync('components/roots-3d.tsx', 'utf8');
assert(roots.includes('id="root-inspect"'));
assert(roots.includes('NativeSelectOption'));
assert(roots.includes("addEventListener('webglcontextlost'"));
assert(roots.includes('data-unavailable={unavailable}'));
console.log(
  'PASS: 1,441 angles × norm checks; rotation commutator limit; U(1) charge winding; SU(2) sign/period; electric charges; invalid inputs; learning prerequisites and keyboard/fallback control wiring. Browser interaction requires separate QA.',
);
