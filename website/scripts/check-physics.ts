import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import {
  particles,
  multiplets,
  anomalyContributions,
  anomalyTotals,
  weakDoublets,
  massFraction,
} from '../lib/particle-physics.ts';
import { readerPaths } from '../lib/reader-paths.ts';
const expected = [
  [2, 2, 3, 6, 6],
  [-1, -4, 0, -192, -12],
  [-1, 2, 0, 24, 6],
  [0, 0, -3, -54, -6],
  [0, 0, 0, 216, 6],
];
expected.forEach((row, i) => assert.deepEqual(anomalyContributions(i), row));
const zeroSpectra = [];
for (let mask = 0; mask < 32; mask++) {
  const included = multiplets.map((_, i) => Boolean(mask & (1 << i)));
  const result = anomalyTotals(included);
  assert.deepEqual(
    result,
    [0, 1, 2, 3, 4].map((j) =>
      expected.reduce((sum, row, i) => sum + (included[i] ? row[j] : 0), 0),
    ),
  );
  if (result.every((n) => n === 0)) zeroSpectra.push(mask);
}
assert.deepEqual(zeroSpectra, [0, 31]);
assert.equal(weakDoublets([true, true, true, true, true]), 4);
assert.equal(weakDoublets([true, true, true, false, true]), 3);
assert.throws(() => anomalyTotals([true]));
assert.throws(() => anomalyContributions(-1));
for (let i = 0; i <= 100; i++) assert.equal(massFraction(i), i / 100);
for (const value of [-1, 101, NaN, Infinity])
  assert.throws(() => massFraction(value));
assert.equal(new Set(particles.map((p) => p.id)).size, 17);
for (const generation of [0, 1, 2]) {
  const family = particles.filter((p) => p.generation === generation);
  assert.equal(family.length, 4);
  assert.deepEqual(
    family.map((p) => p.charge),
    ['+⅔', '−⅓', '−1', '0'],
  );
  assert.equal(family.filter((p) => p.kind === 'neutrino').length, 1);
  assert(family.every((p) => p.spin === '½'));
}
const source = ['research-essay', 'learning-exhibits', 'physics-laboratory']
  .map((f) => readFileSync('components/' + f + '.tsx', 'utf8'))
  .join('\n');
const ids = new Set([...source.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1]));
assert.equal(readerPaths.length, 4);
for (const path of readerPaths) {
  assert(['story', 'explore', 'math'].includes(path.depth));
  for (const stop of path.stops)
    assert(ids.has(stop.id), 'Missing reader-path target: ' + stop.id);
}
const theme = readFileSync('app/themes.css', 'utf8');
assert(!theme.includes('data-theme'), 'No alternate light palette.');
const layout = readFileSync('app/layout.tsx', 'utf8');
assert(
  layout.includes('data-theme="dark"'),
  'Dark on the server, before hydration.',
);
assert(
  !layout.includes('localStorage') && !layout.includes('prefers-color-scheme'),
  'Saved or OS light preference cannot override the page.',
);
assert(!source.includes('ThemeToggle'), 'No light-mode toggle remains.');
const luminance = (hex: string) => {
  const channels = [1, 3, 5]
    .map((i) => parseInt(hex.slice(i, i + 2), 16) / 255)
    .map((x) => (x <= 0.04045 ? x / 12.92 : ((x + 0.055) / 1.055) ** 2.4));
  return channels[0] * 0.2126 + channels[1] * 0.7152 + channels[2] * 0.0722;
};
const contrast = (a: string, b: string) => {
  const [hi, lo] = [luminance(a), luminance(b)].sort((x, y) => y - x);
  return (hi + 0.05) / (lo + 0.05);
};
for (const [fg, bg] of [
  ['f0f2f3', '080b10'],
  ['b2c2d5', '0b111a'],
  ['adc2d9', '122034'],
]) {
  assert(contrast('#' + fg, '#' + bg) >= 4.5, 'Dark body contrast');
}
for (const file of ['globals', 'exhibits', 'physics']) {
  for (const match of readFileSync('app/' + file + '.css', 'utf8').matchAll(
    /var\(--tone-([a-f0-9]+)\)/g,
  ))
    assert(theme.includes('--tone-' + match[1] + ':'), 'Undefined theme token');
}
console.log(
  'PASS: all 32 matter subsets; five anomaly channels; global SU(2) parity; 101 Higgs values and invalid input; 17 gallery entries; four reader paths; theme tokens and representative body-text contrast.',
);
