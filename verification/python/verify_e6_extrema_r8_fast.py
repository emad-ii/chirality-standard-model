#!/usr/bin/env python3
"""Independent E6 check in the standard R^8 realization, using bit masks."""
from collections import Counter, deque
from fractions import Fraction as F
from itertools import product

from verification_checks import require

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
def mask_type(m):
 roots_in=[i for i in range(len(roots)) if (m>>i)&1]
 rem=set(roots_in); sizes=[]
 while rem:
  start=rem.pop(); comp={start}; q=[start]
  while q:
   i=q.pop(); adj={j for j in rem if dot(roots[i],roots[j])!=0}
   rem-=adj; comp|=adj; q.extend(adj)
  sizes.append(len(comp))
 names={2:"A1",6:"A2",12:"A3",20:"A4",30:"A5",40:"D5"}
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
profiles=Counter(); common=Counter(); cell_types={}; P=set(); Q=set()
for wi,d in enumerate(D):
 for ai,a in enumerate(A):
  ar=pair_roots[ai]
  for ti,t in enumerate(T):
   p=((d&a).bit_count(),(d&t).bit_count(),(a&t).bit_count()); n=(d&a&t).bit_count()
   profiles[p]+=1; common[n]+=1
   cell_types.setdefault((p,n),set()).add(mask_type(d&a&t))
   if p==(20,10,14): P.add((d,a,t))
   ar_i=ri[ar]
   if (t>>ar_i)&1:
    factor=sum(1<<j for j,r in enumerate(roots) if ((t>>j)&1) and dot(ar,r)!=0)
   else: factor=0
   char=((t>>ar_i)&1) and dot(weights[wi],ar)==0 and any(((factor>>j)&1) and dot(weights[wi],r)!=0 for j,r in enumerate(roots))
   require((n==10)==bool(char))
   if n==10: Q.add((d,a,t))
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
require(len(P)==4320 and tri_orbit(next(iter(P)))==P)
require(len(Q)==2160 and tri_orbit(next(iter(Q)))==Q)
print('Independent R8 verification passed:',len(roots),len(weights),len(T),len(P),len(Q),'color cells=2')
