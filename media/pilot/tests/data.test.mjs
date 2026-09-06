import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,existsSync} from 'node:fs';
import {candidates,e8Roots,projectionBasis,family,captions,duration,revision} from '../data.mjs';

const companion=new URL('../../../website/lib/e6.ts',import.meta.url);
test('all six coefficient vectors agree with the paper website data',()=>{
  assert(existsSync(companion), 'The website and pilot belong to the same repository');
  const source=readFileSync(companion,'utf8');
  const values=[...source.matchAll(/coefficients: \[([^\]]+)\]/g)].map(m=>m[1].split(',').map(Number));
  assert.deepEqual(candidates.map(c=>c.coefficients),values);
  assert.equal(revision,'launch-2026-09-06');
});
test('normalized SU(N) cubic-index formulas reproduce the displayed coefficients',()=>{
  const factorial=n=>n<2?1:n*factorial(n-1);
  const exterior=(n,k)=>(n-2*k)*factorial(n-3)/(factorial(k-1)*factorial(n-k-1));
  const expected=[[1],[(3+4)*3,-6],[3*3,3*3,3*3],[exterior(6,2)*3,-15],[exterior(9,3)],[0,27]];
  // The E6 zero is the paper's invariant-theory input, not established by this arithmetic test.
  assert.deepEqual(candidates.map(c=>c.coefficients),expected);
});
test('precisely the final row has a zero simple-factor coefficient',()=>{
  assert.deepEqual(candidates.map(c=>c.coefficients.includes(0)),[false,false,false,false,false,true]);
  assert.equal(candidates[5].factors[0],'E₆');
  assert.deepEqual(candidates.map(c=>c.dimensions.reduce((p,x)=>p*x,1)),[3,18,27,45,84,81]);
});
test('the E8 illustration uses 240 distinct actual roots of squared length two',()=>{
  const roots=e8Roots();assert.equal(roots.length,240);assert.equal(new Set(roots.map(r=>r.join(','))).size,240);
  const keys=new Set(roots.map(r=>r.join(',')));
  for(const r of roots){assert.equal(r.length,8);assert.equal(r.reduce((s,x)=>s+x*x,0),2);assert(keys.has(r.map(x=>-x).join(',')));}
});
test('projection basis is orthonormal; visual coordinates are not invented root data',()=>{
  const b=projectionBasis();b.forEach((u,i)=>b.forEach((v,j)=>assert(Math.abs(u.reduce((s,x,k)=>s+x*v[k],0)-(i===j?1:0))<1e-12)));
});
test('branching retains all 81 dimensions rather than deleting the vectorlike states',()=>{
  assert.equal(family.chiral+family.vectorlike+family.singlet,27);
  assert.equal(family.copies*27,81);assert.equal(family.copies*family.chiral,45);
});
test('caption timing covers the pilot without gaps or overlaps',()=>{
  assert.equal(captions[0][0],0);assert.equal(captions.at(-1)[1],duration);
  captions.forEach(([a,b,s],i)=>{assert(b>a);assert(s.length>0);if(i)assert.equal(a,captions[i-1][1]);});
});
test('authoring has no autonomous time, random state or remote assets',()=>{
  const script=readFileSync(new URL('../film.mjs',import.meta.url),'utf8');
  assert(!/Date\.now|Math\.random|requestAnimationFrame|setInterval/.test(script));
  const html=readFileSync(new URL('../index.html',import.meta.url),'utf8');
  assert(!/(?:src|href)="https?:/.test(html));
});
