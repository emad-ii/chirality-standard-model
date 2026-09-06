import { copyFileSync, readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';

const site = fileURLToPath(new URL('../', import.meta.url));
const root = resolve(site, '..');
const files = {
  'paper.pdf': 'paper/paper.pdf',
  'paper.tex': 'paper/paper.tex',
  'Cubic_Anomaly_Master_Verification.ipynb': 'Cubic_Anomaly_Master_Verification.ipynb',
  'e6-certificate.json': 'verification/certificates/e6_extrema_certificate.json',
  'equation-story.mp4': 'media/equations/equation-story.mp4',
  'equation-story.vtt': 'media/equations/equation-story.vtt',
  'equation-poster.jpg': 'media/equations/equation-poster.jpg',
  'one-survivor-pilot.mp4': 'media/pilot/outputs/one-survivor-pilot.mp4',
  'one-survivor-pilot.vtt': 'media/pilot/outputs/one-survivor-pilot.vtt',
};
const check = process.argv.includes('--check');
const manifest = {
  repository: 'https://github.com/emad-ii/chirality-standard-model',
  scope: 'SHA-256 of the downloadable files copied from this checkout. Content identity, not a publisher signature.',
  files: Object.entries(files).map(([download, source]) => {
    const bytes = readFileSync(resolve(root, source));
    const target = resolve(site, 'public', download);
    if (check) {
      if (!bytes.equals(readFileSync(target))) throw new Error('Stale download: ' + download);
    } else copyFileSync(resolve(root, source), target);
    return { download, source, bytes: bytes.length, sha256: createHash('sha256').update(bytes).digest('hex') };
  }),
};
const certificate = readFileSync(resolve(root, files['e6-certificate.json']));
if (check) {
  if (!certificate.equals(readFileSync(resolve(site, 'lib/certificate.json')))) throw new Error('Stale explorer certificate');
} else copyFileSync(resolve(root, files['e6-certificate.json']), resolve(site, 'lib/certificate.json'));
const json = JSON.stringify(manifest, null, 2) + '\n';
const target = resolve(site, 'public/source-manifest.json');
if (check) {
  if (readFileSync(target, 'utf8') !== json) throw new Error('Stale asset manifest');
} else writeFileSync(target, json);
console.log(`${check ? 'Verified' : 'Synced'} ${manifest.files.length} downloads and the explorer certificate against the canonical sources.`);
