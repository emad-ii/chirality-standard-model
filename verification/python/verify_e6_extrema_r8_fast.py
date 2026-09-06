#!/usr/bin/env python3
"""Independent E6 check in the standard R^8 realization, using bit masks."""
from collections import Counter, deque
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations, product

from verification_checks import VerificationFailure, require

def V(*xs): return tuple(F(x) for x in xs)
S=(
 V(F(1,2),-F(1,2),-F(1,2),-F(1,2),-F(1,2),-F(1,2),-F(1,2),F(1,2)),
 V(1,1,0,0,0,0,0,0), V(-1,1,0,0,0,0,0,0),
 V(0,-1,1,0,0,0,0,0), V(0,0,-1,1,0,0,0,0),
 V(0,0,0,-1,1,0,0,0),
)
N=6
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def refl(x,i): return sub(x,tuple(dot(x,S[i])*a for a in S[i]))
def orbit(seed,step):
 q=deque([seed]); seen={seed}
 while q:
  x=q.popleft()
  for i in range(N):
   y=step(x,i)
   if y not in seen: seen.add(y); q.append(y)
 return tuple(seen)
def solve(M,b):
 a=[list(r)+[z] for r,z in zip(M,b)]; n=len(a)
 for c in range(n):
  p=next(r for r in range(c,n) if a[r][c]); a[c],a[p]=a[p],a[c]
  z=a[c][c]; a[c]=[x/z for x in a[c]]
  for r in range(n):
   if r!=c and a[r][c]:
    z=a[r][c]; a[r]=[x-z*y for x,y in zip(a[r],a[c])]
 return tuple(r[-1] for r in a)
C=tuple(tuple(dot(x,y) for y in S) for x in S)
require(C==((2,0,-1,0,0,0),(0,2,0,-1,0,0),(-1,0,2,-1,0,0),(0,-1,-1,2,-1,0),(0,0,0,-1,2,-1),(0,0,0,0,-1,2)))
roots=sorted(orbit(S[0],refl)); ri={r:i for i,r in enumerate(roots)}; require(len(roots)==72)
perms=tuple(tuple(ri[refl(r,j)] for r in roots) for j in range(N))
def pmask(m,p):
 out=0
 while m:
  b=m & -m; i=b.bit_length()-1; out |= 1<<p[i]; m-=b
 return out
@lru_cache(maxsize=4096)
def mask_type(m):
 require(type(m) is int and 0 <= m < (1<<len(roots)), "invalid root mask")
 roots_in=[i for i in range(len(roots)) if (m>>i)&1]
 rem=set(roots_in); sizes=[]
 while rem:
  start=rem.pop(); comp={start}; q=[start]
  while q:
   i=q.pop(); adj={j for j in rem if dot(roots[i],roots[j])!=0}
   rem-=adj; comp|=adj; q.extend(adj)
  sizes.append(len(comp))
 names={2:"A1",6:"A2",12:"A3",20:"A4",30:"A5",40:"D5"}
 require(all(n in names for n in sizes), "unsupported root component")
 return "+".join(names[n] for n in sorted(sizes,reverse=True))

def mask_orbit(seed):
 q=deque([seed]); seen={seed}
 while q:
  m=q.popleft()
  for p in perms:
   n=pmask(m,p)
   if n not in seen: seen.add(n); q.append(n)
 return tuple(seen)
omega_c=solve(C,(F(1),0,0,0,0,0)); omega=tuple(sum(omega_c[j]*S[j][k] for j in range(N)) for k in range(8))
weights=orbit(omega,refl); require(len(weights)==27)
D=[]
for w in weights: D.append(sum(1<<i for i,r in enumerate(roots) if dot(w,r)==0))
pair_roots=[]
seen=set()
for r in roots:
 if r in seen: continue
 a=min(r,neg(r)); seen|={a,neg(a)}; pair_roots.append(a)
A=[]
for a in pair_roots: A.append(sum(1<<i for i,r in enumerate(roots) if r in (a,neg(a)) or dot(a,r)==0))
def coeff(r): return solve(C,tuple(dot(r,a) for a in S))
theta0=sum(1<<i for i,r in enumerate(roots) if coeff(r)[3]%3==0)
T=mask_orbit(theta0); require((len(set(D)),len(set(A)),len(T))==(27,36,40))

# Independent exact R8 calculations: no primary selector, rank or d_chi imports.
negative_indices=tuple(ri[neg(r)] for r in roots)
sum_indices=tuple(tuple(ri.get(tuple(x+y for x,y in zip(a,b))) for b in roots) for a in roots)
weight_pairings=tuple(tuple(dot(w,r) for r in roots) for w in weights)
require(all(x in (-1,0,1) for row in weight_pairings for x in row),
        "27 must be minuscule on every ambient coroot")
require(all(refl(w,i) in weights for w in weights for i in range(N)),
        "27 character must be Weyl invariant")

def span_rank(vectors):
 rows=[list(row) for row in vectors]; rank=0
 for c in range(8):
  pivot=next((j for j in range(rank,len(rows)) if rows[j][c]),None)
  if pivot is None: continue
  rows[rank],rows[pivot]=rows[pivot],rows[rank]
  scale=rows[rank][c]; rows[rank]=[x/scale for x in rows[rank]]
  for j in range(rank+1,len(rows)):
   scale=rows[j][c]
   if scale: rows[j]=[x-scale*y for x,y in zip(rows[j],rows[rank])]
  rank+=1
 return rank

@lru_cache(maxsize=4096, typed=True)
def mask_structure(m):
 require(type(m) is int and 0 < m < (1<<len(roots)), "invalid pair-parent mask")
 indices=[i for i in range(len(roots)) if (m>>i)&1]
 require(all((m>>negative_indices[i])&1 for i in indices)
         and all(sum_indices[i][j] is None or (m>>sum_indices[i][j])&1
                 for i in indices for j in indices), "parent mask is not closed")
 rank=span_rank([roots[i] for i in indices]); kind=mask_type(m)
 require((kind,rank) in {("A4",4),("A3+A1+A1",5),("A2+A1+A1",4),
                       ("A2+A2+A1",5),("A1+A1+A1",3)}, "unsupported pair parent")
 # Minuscule weights and ambient Weyl invariance imply a sum of minuscule
 # parent characters. Their disjoint orbits make opposite cancellation d_chi.
 character=Counter(tuple(row[i] for i in indices) for row in weight_pairings)
 dchi=sum(max(n-character.get(neg(w),0),0) for w,n in character.items())
 return len(indices),rank,len(indices)+rank,dchi

def strict_greatest(scores):
 require(isinstance(scores,(tuple,list)) and len(scores)==3
         and all(type(x) is int and x>=0 for x in scores), "invalid selector scores")
 winners=[i for i in range(3) if all(scores[i]>scores[j] for j in range(3) if j!=i)]
 require(len(winners)==1, "greatest score is tied")
 return winners[0]

def select_intrinsic_pair(parents):
 require(isinstance(parents,(tuple,list)) and len(parents)==3
         and all(type(m) is int for m in parents), "expected three parent masks")
 data=tuple(mask_structure(m) for m in parents)
 root_winner=strict_greatest(tuple(row[0] for row in data))
 require(root_winner==strict_greatest(tuple(row[2] for row in data)),
         "root-count and semisimple-dimension selectors disagree")
 return root_winner

def rejects(function,*args,reason):
 try: function(*args)
 except VerificationFailure as error: require(reason in str(error), "unexpected rejection")
 else: require(False, ("accepted invalid input",function.__name__,reason))

for bad in ((),(1,2),(1,2,3,4),"123",{0:1,1:2,2:3},(True,2,3),(1.0,2,3),(-1,2,3)):
 rejects(strict_greatest,bad,reason="invalid selector scores")
for tied in ((20,20,10),(24,14,24),(0,0,0)):
 rejects(strict_greatest,tied,reason="tied")
for bad in (None,(),(1,2),(1,2,True),(1,2,[])):
 rejects(select_intrinsic_pair,bad,reason="three parent masks")
for bad in (0,-1,True,1.0,1<<len(roots)):
 rejects(mask_structure,bad,reason="invalid pair-parent mask")
rejects(mask_structure,1,reason="not closed")
rejects(mask_structure,(1<<ri[S[0]]) | (1<<ri[neg(S[0])]),reason="unsupported pair parent")
rejects(mask_structure,(1<<len(roots))-1,reason="unsupported root component")
alpha,beta=S[0],S[2]
rejects(mask_structure,sum(1<<ri[r] for r in (alpha,neg(alpha),beta,neg(beta))),reason="not closed")

parents={x&y for left,right in ((D,A),(D,T),(A,T)) for x,y in product(left,right)}
require(len(parents)==2466, "complete independent pair-parent universe")
structure={m:mask_structure(m) for m in parents}
require(Counter((mask_type(m),*row) for m,row in structure.items())==Counter({
 ("A4",20,4,24,15):216, ("A3+A1+A1",16,5,21,16):270,
 ("A2+A1+A1",10,4,14,12):1080, ("A2+A2+A1",14,5,19,27):360,
 ("A1+A1+A1",6,3,9,0):540}), "independent types, ranks, dimensions and d_chi")
for m,row in structure.items():
 for p in perms:
  image=pmask(m,p)
  require(image in structure and structure[image]==row and mask_type(image)==mask_type(m),
          "pair-parent invariance under every simple reflection")

profiles=Counter(); common=Counter(); cell_types={}; cells={}; P=set(); Q=set()
rank_winners=Counter(); chiral_winners=Counter(); selector_examples={}
for wi,d in enumerate(D):
 for ai,a in enumerate(A):
  ar=pair_roots[ai]
  for ti,t in enumerate(T):
   pair_masks=(d&a,d&t,a&t); data=tuple(structure[m] for m in pair_masks)
   selected=select_intrinsic_pair(pair_masks)
   require(selected==0, "DA must be the unique structural greatest pair")
   require(tuple(i for i,row in enumerate(data) if row[3] in (15,16))==(selected,),
           "structural selector iff d_chi is 15 or 16")
   ranks=tuple(row[1] for row in data)
   rank_winners[tuple(i for i,r in enumerate(ranks) if r==max(ranks))]+=1
   chiral_winners[strict_greatest(tuple(row[3] for row in data))]+=1
   p=((d&a).bit_count(),(d&t).bit_count(),(a&t).bit_count()); n=(d&a&t).bit_count()
   selector_examples.setdefault((p,n),pair_masks)
   profiles[p]+=1; common[n]+=1
   cell_types.setdefault((p,n),set()).add(mask_type(d&a&t))
   cells.setdefault((p,n),set()).add((d,a,t))
   if p==(20,10,14): P.add((d,a,t))
   ar_i=ri[ar]
   if (t>>ar_i)&1:
    factor=sum(1<<j for j,r in enumerate(roots) if ((t>>j)&1) and dot(ar,r)!=0)
   else: factor=0
   char=((t>>ar_i)&1) and dot(weights[wi],ar)==0 and any(((factor>>j)&1) and dot(weights[wi],r)!=0 for j,r in enumerate(roots))
   require((n==10)==bool(char))
   if n==10: Q.add((d,a,t))
require(sum(profiles.values())==38880, "all independent triples checked")
require(rank_winners==Counter({(0,):16200,(2,):4320,(0,1):12960,(0,2):5400}),
        "rank alone must exhibit ties and wrong selections")
require(chiral_winners==Counter({0:29160,2:9720}), "chiral maximum is a different selector")
for example in selector_examples.values():
 for order in permutations(range(3)):
  require(select_intrinsic_pair(tuple(example[i] for i in order))==order.index(0),
          "selector depends on pair labelling")
 rejects(select_intrinsic_pair,(example[0],example[0],example[1]),reason="tied")
require(profiles==Counter({(20,10,14):4320,(20,10,6):12960,(16,10,14):5400,(16,10,6):16200}))
require(common==Counter({2:12960,4:12960,6:6480,8:4320,10:2160}))
require(cell_types=={
 ((16,10,6),2):{"A1"}, ((20,10,6),4):{"A1+A1"},
 ((16,10,6),6):{"A1+A1+A1"}, ((16,10,14),6):{"A1+A1+A1"},
 ((20,10,14),8):{"A2+A1"}, ((16,10,14),10):{"A2+A1+A1"},
})
def tri_orbit(seed):
 q=deque([seed]); seen={seed}
 while q:
  x=q.popleft()
  for p in perms:
   y=tuple(pmask(m,p) for m in x)
   if y not in seen: seen.add(y); q.append(y)
 return seen
def verify_cell_orbit(cell):
 require(bool(cell), "empty profile cell")
 require(tri_orbit(min(cell))==cell, "Weyl orbit differs from profile cell")

def verify_cell_partition(cell_sets,universe):
 covered=set()
 for cell in cell_sets:
  require(covered.isdisjoint(cell), "profile cells overlap")
  covered.update(cell)
 require(covered==universe, "profile cells do not exhaust triple universe")

cell_sizes={
 ((16,10,6),2):12960, ((20,10,6),4):12960,
 ((16,10,6),6):3240, ((16,10,14),6):3240,
 ((20,10,14),8):4320, ((16,10,14),10):2160,
}
require({key:len(cell) for key,cell in cells.items()}==cell_sizes,
        "all six independent profile-cell cardinalities")
universe=set(product(D,A,T))
require(len(universe)==38880, "complete independent triple universe")
verify_cell_partition(cells.values(),universe)
for key in cell_sizes:
 verify_cell_orbit(cells[key])
require(len(P)==4320 and P==cells[((20,10,14),8)])
require(len(Q)==2160 and Q==cells[((16,10,14),10)])

# Reuse the smallest cells to bound the cost of false-positive controls.
q_key=((16,10,14),10); other_key=((16,10,14),6); removed=min(Q)
rejects(verify_cell_orbit,{removed},reason="Weyl orbit differs from profile cell")
rejects(verify_cell_orbit,Q|cells[other_key],reason="Weyl orbit differs from profile cell")
missing=dict(cells); missing[q_key]=Q-{removed}
rejects(verify_cell_partition,missing.values(),universe,
        reason="profile cells do not exhaust triple universe")
overlapping=dict(cells); overlapping[other_key]=cells[other_key]|{removed}
rejects(verify_cell_partition,overlapping.values(),universe,reason="profile cells overlap")

print('Independent R8 verification passed:',len(roots),len(weights),len(T),len(P),len(Q),'color cells=2')
print('Independent R8 structural ordering PASS: 38880 triples, 2466 parents; roots and rank+roots '
      'uniquely select H_DA iff d_chi in {15,16}')
print(f'Independent R8 orbit partition PASS: {len(cells)} cells, {len(universe)} triples; '
      f'sizes={",".join(str(len(cells[key])) for key in cell_sizes)}; negative controls=4')
