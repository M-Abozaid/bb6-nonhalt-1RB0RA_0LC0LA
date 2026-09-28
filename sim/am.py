# Abstract model of M8 checkpoints (round 3). digits LSB-first ints 0/1/2.
# state = (k, C, m, L): C = ('cl', ds) | ('lone', lo, hi); L = [(bit, block)] ; B1 = k+1+m
import sys
Lu=[0,1,1,1]; Rr=[0,0,1,1]
def rdig(d): return [[0,0,0],[0,1,1],[0,0,1]][d]
def Sr(ds): return [c for d in ds for c in rdig(d)]
def ctape(C):
    if C[0]=='cl': return Sr(C[1])
    return Sr(C[1])+[1]+Sr(C[2])
def lad(L):
    out=[]
    for s,b in L: out+=([1,0] if s else [0,0])+Lu*b
    return out+[1,0]
def val(ds): return sum(d*3**i for i,d in enumerate(ds))
def inc(ds):
    ds=list(ds); i=0
    while i<len(ds) and ds[i]==2: ds[i]=0; i+=1
    if i==len(ds): ds.append(1)
    else: ds[i]+=1
    return ds
def lowok(ds): return any(d!=2 for d in ds)
def linc(B,L):
    if not L: return B-2,[(0,2)]
    s,c=L[0]
    if not s: return B,[(1,c)]+L[1:]
    c2,r2=linc(c,L[1:])
    return B-2,[(0,c2+2)]+r2
def sh(ds):
    # [f] ++ Sr ds  re-read
    a=0
    while a<len(ds) and ds[a]==0: a+=1
    if a==len(ds): return ('cl',[0]*a)   # + trailing blank
    d=ds[a]
    return ('lone',[0]*a+[2 if d==1 else 0],ds[a+1:])
def cph(C):
    """counter phase: returns (k', C')"""
    if C[0]=='cl': return 0,('cl',inc(C[1]))
    lo,hi=C[1],C[2]
    if lowok(lo): return 0,('lone',inc(lo),hi)
    n=len(lo)
    if n>=1: return 1,('cl',[0]*(n-1)+inc(hi))
    return 0,sh(inc(inc(hi)))
def astep(S):
    k,C,m,L=S
    B=k+1+m
    p,L2=linc(B,L)
    if p>=1:
        k2,C2=cph(C)
        return (k2,C2,p-1,L2),'R' if k2==1 else ('0' if C[0]=='lone' and not C[1] else '')
    assert p==0 and C[0]=='cl' and L2[0][0]==0, ('BAD',S)
    b=L2[0][1]; rest=L2[1:]
    W=inc(inc(C[1]))
    if not W: W=[0]
    d0,r=W[0],W[1:]
    if d0==0: return (1,sh(r),b-1,rest),'A'
    if d0==2: return (1,('lone',[],r),b-1,rest),'A'
    return (0,sh(inc(r)),b,rest),'A'
def render(S):
    """(left tape list nearest-first excluding head, head cell, right list, state) as hc"""
    k,C,m,L=S
    P=Rr*k+ctape(C)
    R=Lu*m+lad(L)
    return ('B',[1]+P,1,[1,1]+R)
