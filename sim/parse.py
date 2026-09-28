from am import *
from tm import trim
RD={(0,0,0):0,(0,1,1):1,(0,0,1):2}
def pdigits(cells):
    cells=list(cells)
    if len(cells)%3: return None
    ds=[]
    for i in range(0,len(cells),3):
        t=tuple(cells[i:i+3])
        if t not in RD: return None
        ds.append(RD[t])
    return ds
def pctape(P):
    P=trim(P); out=[]
    for pad in range(3):
        Q=P+[0]*pad
        d=pdigits(Q)
        if d is not None: out.append(('cl',d))
        for i in range(0,len(Q),3):
            if Q[i]==1:
                lo=pdigits(Q[:i]); 
                rest=Q[i+1:]; rest=rest+[0]*((-len(rest))%3)
                hi=pdigits(rest)
                if lo is not None and hi is not None: out.append(('lone',lo,hi))
    return out
def plad(R):
    R=trim(R); m=0
    while R[4*m:4*m+4]==Lu: m+=1
    R=R[4*m:]; L=[]
    while True:
        if R==[1] or R==[1,0]: return m,L
        if len(R)<2 or R[1]!=0: return None
        s=R[0]; R=R[2:]; b=0
        while R[4*b:4*b+4]==Lu: b+=1
        R=R[4*b:]; L.append((s,b))
def parse(L,R):
    """L nearest-first (after head), R after head; head B on 1 with L[0]=1,R[:2]=[1,1]"""
    if not(L and L[0]==1 and R[:2]==[1,1]): return []
    pl=plad(R[2:])
    if pl is None: return []
    m,Ld=pl; P=L[1:]; out=[]
    for k in (0,1):
        if k==1 and P[:4]!=Rr: break
        for C in pctape(P[4*k:]): out.append((k,C,m,Ld))
    return out
