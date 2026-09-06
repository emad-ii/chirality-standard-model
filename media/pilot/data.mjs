// Table 1 of paper/paper.tex in this repository.
// These are the final six full-rank rows, NOT the original classification domain.
export const revision = 'launch-2026-09-06';
export const candidates = [
  { g: '\\mathfrak g_2', h: '\\mathfrak{su}(3)', v: '\\mathbf3', dimensions: [3], coefficients: [1], factors: ['A₂'], radical: '0' },
  { g: '\\mathfrak f_4', h: '\\mathfrak{su}(3)\\oplus\\mathfrak{su}(3)', v: '\\mathbf6\\boxtimes\\overline{\\mathbf3}', dimensions: [6,3], coefficients: [21,-6], factors: ['A₂','A₂'], radical: '0' },
  { g: '\\mathfrak e_6', h: '\\mathfrak{su}(3)^{\\oplus3}', v: '\\mathbf3\\boxtimes\\mathbf3\\boxtimes\\mathbf3', dimensions: [3,3,3], coefficients: [9,9,9], factors: ['A₂','A₂','A₂'], radical: '0' },
  { g: '\\mathfrak e_7', h: '\\mathfrak{su}(6)\\oplus\\mathfrak{su}(3)', v: '\\mathbf{15}\\boxtimes\\overline{\\mathbf3}', dimensions: [15,3], coefficients: [6,-15], factors: ['A₅','A₂'], radical: '0' },
  { g: '\\mathfrak e_8', h: '\\mathfrak{su}(9)', v: '\\Lambda^3\\mathbf9', dimensions: [84], coefficients: [9], factors: ['A₈'], radical: '0' },
  { g: '\\mathfrak e_8', h: '\\mathfrak e_6\\oplus\\mathfrak{su}(3)_M', v: '\\mathbf{27}\\boxtimes\\mathbf3', dimensions: [27,3], coefficients: [0,27], factors: ['E₆','A₂'], radical: 'E₆' },
];

export const duration = 78;
export const captions = [
  [0, 7, 'After the structural reduction, the full-rank branch has six candidates.'],
  [7, 15, 'These two coefficients belong to different factors. Their opposite signs do not cancel.'],
  [15, 24, 'For these semisimple rows, mixed terms vanish. Each coefficient tests its own simple factor.'],
  [24, 32, 'Opposite signs on different factors do not cancel: they are different tensor components.'],
  [32, 41, 'Five rows have no zero coefficient. Their radicals vanish.'],
  [41, 49, 'In the final row, the E₆ coefficient is zero. The SU(3) coefficient is 27.'],
  [49, 57, 'E₆ is the radical. SU(3) remains a background global symmetry with a cubic anomaly.'],
  [57, 65, 'The representation is 27 tensor 3. Restricted to E₆, it becomes three copies of the 27.'],
  [65, 73, 'Along the paper’s Standard Model embedding, each 27 gives a family, a conjugate pair and two singlets.'],
  [73, 78, 'Three net chiral Standard Model families, up to conjugation.'],
];

// The 240 roots of E8 in the standard Euclidean R8 realisation.
// They are used only for a labelled mathematical projection, not as particle paths.
export function e8Roots() {
  const roots=[];
  for(let i=0;i<8;i++) for(let j=i+1;j<8;j++) for(const a of [-1,1]) for(const b of [-1,1]) {
    const r=Array(8).fill(0); r[i]=a; r[j]=b; roots.push(r);
  }
  for(let mask=0;mask<256;mask++) {
    const r=Array.from({length:8},(_,i)=>(mask>>i)&1 ? -.5 : .5);
    if(r.filter(x=>x<0).length%2===0) roots.push(r);
  }
  return roots;
}

export function projectionBasis() {
  const basis=[];
  for(let k=0;k<3;k++) {
    let v=Array.from({length:8},(_,i)=>Math.sin((i+1)*(k+1)*1.137)+Math.cos((i+2)*(k+2)*.731));
    for(const u of basis) {const d=v.reduce((s,x,i)=>s+x*u[i],0); v=v.map((x,i)=>x-d*u[i]);}
    const n=Math.hypot(...v); basis.push(v.map(x=>x/n));
  }
  return basis;
}

export const family = {chiral:15, vectorlike:10, singlet:2, copies:3};
