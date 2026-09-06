import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import {
  readerPaths,
  chapterInfo,
  chapterForAnchor,
  decodeAnchor,
  omittedChapters,
  resolvePath,
} from '../lib/reader-paths.ts';
import { motionAllowed, nextHiggsFrame } from '../lib/motion-policy.ts';
import { chiralPacket, transverseWave } from '../lib/scene-geometry.ts';

const chapters = Object.keys(chapterInfo).sort();
for (const path of readerPaths) {
  assert.equal(
    new Set(path.chapters).size,
    path.chapters.length,
    path.id + ': no repeated chapter',
  );
  assert.deepEqual(
    [...path.chapters, ...omittedChapters(path.id)].sort(),
    chapters,
    path.id + ': no content lost',
  );
  for (const required of [
    'argument',
    'selection',
    'geometry',
    'families',
    'verify',
  ])
    assert(path.chapters.includes(required as (typeof path.chapters)[number]));
  assert(
    path.chapters.indexOf('geometry') < path.chapters.indexOf('families'),
    'Subgroup geometry precedes restriction',
  );
  assert(
    path.chapters.indexOf('argument') < path.chapters.indexOf('families'),
    'Hypotheses precede interpretation',
  );
  for (const stop of path.stops) assert(path.chapters.includes(stop.id));
  for (const chapter of Object.keys(path.bridges))
    assert(path.chapters.includes(chapter as (typeof path.chapters)[number]));
  assert.equal(resolvePath(path.id), path);
}
assert.equal(resolvePath('curious').chapters[0], 'question');
assert.equal(resolvePath('physics').chapters[0], 'physics');
assert.equal(resolvePath('mathematics').chapters[0], 'argument');
assert.equal(resolvePath('review').chapters[0], 'verify');
assert.equal(resolvePath('invalid').id, 'curious');
assert.equal(resolvePath(null).id, 'curious');
assert.equal(chapterForAnchor('anomalies'), 'physics');
assert.equal(chapterForAnchor('cubic-test'), 'argument');
assert.equal(chapterForAnchor('toString'), undefined);
assert.equal(chapterForAnchor('unknown'), undefined);
assert.equal(decodeAnchor('#%E0%A4%A'), '');
assert.equal(decodeAnchor('#cubic-test'), 'cubic-test');
for (let mask = 0; mask < 16; mask++) {
  const bits = [0, 1, 2, 3].map((i) => Boolean(mask & (1 << i)));
  assert.equal(motionAllowed(bits[0], bits[1], bits[2], bits[3]), mask === 12);
}
let frame = { value: 0, direction: 1 };
const values = new Set<number>();
for (let i = 0; i < 200; i++) {
  values.add(frame.value);
  frame = nextHiggsFrame(frame.value, frame.direction);
  assert(frame.value >= 0 && frame.value <= 100);
}
assert.deepEqual(
  [...values].sort((a, b) => a - b),
  Array.from({ length: 11 }, (_, i) => i * 10),
);
for (const phase of [0, 0.5, Math.PI, Math.PI * 2]) {
  const left = chiralPacket(-1, phase),
    right = chiralPacket(1, phase);
  assert.equal(left.length, 121);
  left.forEach(([x, y, z], i) => {
    assert.deepEqual(right[i], [x, y, -z]);
    assert([x, y, z].every(Number.isFinite));
  });
  const wave = transverseWave(phase);
  assert(wave.flat().every(Number.isFinite));
  assert(wave.every((p) => p[2] === 0));
}
assert.throws(() => chiralPacket(1, NaN));
assert.throws(() => transverseWave(0, 0));
const main = readFileSync('components/research-essay.tsx', 'utf8');
for (const chapter of chapters)
  assert(
    main.includes('chapter="' + chapter + '"'),
    'Missing chapter slot ' + chapter,
  );
const reader = readFileSync('components/reader-paths.tsx', 'utf8');
assert(
  reader.includes('path.chapters.map'),
  'Reader order is actual document order',
);
assert(
  reader.includes('expanded.includes(chapter) ? chapters.get(chapter) : null'),
  'Closed extras are unmounted',
);
assert(
  main.includes("new URL(location.href).searchParams.get('path')") &&
    main.includes("window.addEventListener('popstate', restore)"),
  'Static Pages restores the requested reading path and browser history',
);
console.log(
  'PASS: four distinct reading routes; all chapters retained; prerequisite order; deep-link mapping; invalid URLs; all 16 motion-policy states; 200 Higgs demo steps; mirrored finite wave geometry.',
);
