import { candidates, duration, captions, e8Roots, projectionBasis, family } from './data.mjs';

window.__renderReady=false;
const renderMath = (el,tex) => katex.render(tex,el,{throwOnError:true,output:'html',strict:'error'});
const grid=document.querySelector('#candidate-grid');
candidates.forEach((row,i)=>{
  const el=document.createElement('div'); el.className='candidate'; el.id=`candidate-${i}`;
  el.innerHTML=`<span class="row-id">0${i+1}</span><div class="pair"></div><div class="rep"></div><div class="ports"></div><div class="row-result">${i===5 ? 'radical = E₆' : 'radical = 0'}</div>`;
  renderMath(el.querySelector('.pair'),`${row.g}\\supset ${row.h}`);
  renderMath(el.querySelector('.rep'),`V=${row.v}`);
  row.coefficients.forEach((a,j)=>{
    const port=document.createElement('div');port.className=`port ${a===0?'zero':''}`;
    const factorName={'A₂':'su(3)','A₅':'su(6)','A₈':'su(9)','E₆':'E₆'}[row.factors[j]];
    port.innerHTML=`<div class="coefficient">${a}</div><div class="pulse"></div><span class="factor">${factorName}</span>`;
    el.querySelector('.ports').append(port);
  });
  grid.append(el);
});
for(const el of document.querySelectorAll('[data-tex]')) renderMath(el,el.dataset.tex);
// KaTeX builds ≠ by placing its slash over =. This single glyph's overlap is intentional.
// Keep overlap checking active for every other formula and text block.
document.querySelector('#condition .rlap .mrel').dataset.layoutAllowOverlap='true';

for(let i=0;i<family.copies;i++) {
  const group=document.createElement('div');group.className='family-group';group.id=`family-${i}`;
  group.innerHTML=`<div class="family-label">COPY ${i+1} <span>·</span> 27</div><div class="family-dots"></div>`;
  for(let j=0;j<27;j++) {
    const dot=document.createElement('div');
    dot.className=`basis-dot ${j<15?'chiral':j<25?'vectorlike':'singlet'}`;
    group.querySelector('.family-dots').append(dot);
  }
  document.querySelector('#family-groups').append(group);
}
const rootData=e8Roots(), basis=projectionBasis();
const rootElements=rootData.map(()=>{
  const el=document.createElementNS('http://www.w3.org/2000/svg','circle');
  el.setAttribute('fill','#e6c689');document.querySelector('#root-points').append(el);return el;
});
function drawRoots(time) {
  const angle=.27+(time-47)*.085;
  const c=Math.cos(angle),s=Math.sin(angle);
  rootData.forEach((r,i)=>{
    const rotated=[...r];rotated[0]=r[0]*c-r[3]*s;rotated[3]=r[0]*s+r[3]*c;
    const v=basis.map(u=>u.reduce((sum,x,j)=>sum+x*rotated[j],0));
    const depth=(v[2]+Math.SQRT2)/(2*Math.SQRT2);
    rootElements[i].setAttribute('cx',440+v[0]*240);
    rootElements[i].setAttribute('cy',335-v[1]*240);
    rootElements[i].setAttribute('r',2.6+depth*4.2);
    rootElements[i].setAttribute('opacity',.16+depth*.8);
  });
}

const tl=window.__timelines['one-survivor'];
tl.set('#atlas',{autoAlpha:1},0);
tl.fromTo('#atlas h1',{opacity:0,y:20},{opacity:1,y:0,duration:1.2,ease:'power2.out'},0);
tl.fromTo('#condition',{opacity:0},{opacity:1,duration:1.3},2);
tl.fromTo('.candidate',{opacity:0,y:32},{opacity:1,y:0,duration:1,stagger:.22,ease:'power2.out'},3);
tl.fromTo('.ports',{opacity:0},{opacity:1,duration:1.2,stagger:.2},8);
// Teach one worked row before the full comparison. The other rows temporarily leave the frame.
tl.to('.candidate:not(#candidate-1)',{autoAlpha:0,duration:.65},7.2);
tl.to('#candidate-1',{scale:1.55,y:80,duration:1.1,ease:'power2.inOut'},7.4);
tl.to('#candidate-1',{scale:1,y:0,duration:1.1,ease:'power2.inOut'},14.6);
tl.to('.candidate:not(#candidate-1)',{autoAlpha:1,duration:.8},15.2);
tl.fromTo('#atlas-note',{opacity:0},{opacity:1,duration:1},12);
for(let i=0;i<6;i++) {
  tl.fromTo(`#candidate-${i} .pulse`,{opacity:.8,scale:1},{opacity:0,scale:1.7,duration:2.5,ease:'power1.out'},15+i*2.8);
}
tl.to('#factor-note',{opacity:1,duration:.7},24);
tl.to('#candidate-1 .coefficient, #candidate-3 .coefficient',{borderColor:'#e7ad8f',duration:.5},24);
tl.to('#factor-note',{opacity:0,duration:.7},31);
for(let i=0;i<5;i++) {
  tl.to(`#candidate-${i} .row-result`,{opacity:1,duration:.5},32+i*1.35);
  tl.to(`#candidate-${i}`,{opacity:.32,duration:1.2},33+i*1.35);
}
tl.to('#candidate-5',{borderTopColor:'#e6c689',duration:1.3},40);
tl.to('#candidate-5 .row-result',{opacity:1,duration:.8},41);
tl.fromTo('#candidate-5 .zero .pulse',{opacity:1,scale:1},{opacity:0,scale:2.2,duration:3},41);
tl.to('#atlas',{autoAlpha:0,y:-25,duration:.8},46.3);
tl.fromTo('#survivor',{autoAlpha:0,y:25},{autoAlpha:1,y:0,duration:1.1,ease:'power2.out'},47);
tl.fromTo('#root-view',{opacity:0,scale:.93},{opacity:1,scale:1,duration:2.2,ease:'power2.out'},47.5);
tl.fromTo('.radical-result',{opacity:0},{opacity:1,duration:1.1},49);
tl.fromTo('.survivor-definition',{opacity:0},{opacity:1,duration:1},51);
tl.fromTo('.global-note',{opacity:0},{opacity:1,duration:1},51.5);
tl.to('#survivor',{autoAlpha:0,y:-20,duration:.8},56.3);
tl.fromTo('#copies',{autoAlpha:0,y:20},{autoAlpha:1,y:0,duration:1,ease:'power2.out'},57);
tl.fromTo('.copies-formula',{opacity:0},{opacity:1,duration:1},57.5);
tl.fromTo('.family-group',{opacity:0,y:35},{opacity:1,y:0,duration:1.3,stagger:.65,ease:'power2.out'},59);
tl.fromTo('.basis-dot',{scale:.1},{scale:1,duration:.7,stagger:.012,ease:'power2.out'},59);
tl.fromTo('#branching-context, #branching, #family-legend',{opacity:0},{opacity:1,duration:1.2,stagger:.3},65);
tl.to('#index-result',{opacity:1,duration:1},72);
tl.to('#index-note',{opacity:1,duration:.8},73);
tl.fromTo('#progress',{scaleX:0},{scaleX:1,duration,ease:'none'},0);
// All time-varying DOM content is a pure function of the playhead, including reverse seeks.
function updateFrame() {
  const time=tl.time();
  const cue=captions.find(([start,end])=>time>=start&&time<end)||captions.at(-1);
  document.querySelector('#caption').textContent=cue[2];
  document.querySelector('#source-note').textContent=time<47
    ?'Paper §3 · Table 1 · full-rank branch after structural reduction'
    :time<57?'Paper Theorem 2.1 · uniqueness within the stated homogeneous domain'
    :'Paper §§4–5 · branching and net chiral class';
  if(time>=46&&time<=58) drawRoots(time);
}
tl.eventCallback('onUpdate',updateFrame);
drawRoots(47);updateFrame();
await document.fonts.ready;
window.__timelines=window.__timelines||{};
window.__timelines['one-survivor']=tl;
window.__renderReady=true;
