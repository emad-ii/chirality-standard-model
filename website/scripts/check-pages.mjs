import assert from 'node:assert/strict';
import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs';
import { resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { JSDOM } from 'jsdom';

const base = '/chirality-standard-model/';
const output = resolve('dist/client/chirality-standard-model');
const html = readFileSync(resolve(output, 'index.html'), 'utf8');
const doc = new JSDOM(html).window.document;
assert.match(doc.title, /From Chirality to the Standard Model/);
assert.equal(doc.querySelector('link[rel=canonical]').href, 'https://emad-ii.github.io' + base);
assert.match(doc.body.textContent, /April 2026/);
assert.match(doc.body.textContent, /Impose the two conditions together/);
assert.doesNotMatch(doc.body.textContent, /paper states the interpretation explicitly|Identifying V with the full chiral matter module/);
let references = 0;
for (const element of doc.querySelectorAll('[src],[href],[poster]')) {
  for (const attr of ['src', 'href', 'poster']) {
    const url = element.getAttribute(attr);
    if (!url || /^(?:https?:|data:|mailto:|#)/.test(url)) continue;
    assert(url.startsWith(base), 'Missing Pages prefix: ' + url);
    const path = decodeURIComponent(url.slice(base.length).split(/[?#]/)[0]);
    assert(existsSync(resolve(output, path || 'index.html')), 'Missing published file: ' + url);
    references++;
  }
}
const manifest = JSON.parse(readFileSync(resolve(output, 'source-manifest.json'), 'utf8'));
for (const file of manifest.files) {
  const bytes = readFileSync(resolve(output, file.download));
  assert.equal(bytes.length, file.bytes);
  assert.equal(createHash('sha256').update(bytes).digest('hex'), file.sha256);
  assert(bytes.equals(readFileSync(resolve('..', file.source))), 'Published copy differs: ' + file.download);
}
function walk(dir) {
  return readdirSync(dir).flatMap(name => {
    const path = resolve(dir, name);
    assert(!/^(?:\.git|\.env.*|node_modules|wrangler\.json)$/.test(name), 'Private or server file in public output: ' + path);
    return statSync(path).isDirectory() ? walk(path) : [path];
  });
}
const files = walk(output);
for (const path of files.filter(path => path.endsWith('.css'))) {
  const css = readFileSync(path, 'utf8');
  for (const match of css.matchAll(/url\(["']?(\/[^)"']+)["']?\)/g)) {
    assert(match[1].startsWith(base), 'CSS resource lacks project prefix');
    assert(existsSync(resolve(output, match[1].slice(base.length))), 'Missing CSS resource: ' + match[1]);
  }
}
assert(!existsSync(resolve(output, 'chirality-standard-model.zip')), 'Do not ship a second stale repository archive');
console.log(`PASS: static Pages export; ${references} local references; ${manifest.files.length} byte-identical downloads; ${files.length} public files; metadata and current argument text.`);
