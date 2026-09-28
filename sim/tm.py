# M8 machine on dict-free arrays, config compare up to trailing blanks
TR={('A',0):(1,1,'B'),('A',1):(0,1,'A'),('B',0):(0,-1,'C'),('B',1):(0,-1,'A'),('C',0):(1,1,'F'),('C',1):(1,-1,'D'),
    ('D',0):(1,-1,'E'),('D',1):(0,-1,'D'),('E',0):(1,-1,'C'),('E',1):(1,-1,'F'),('F',1):(1,1,'A')}
def trim(l):
    l=list(l)
    while l and l[-1]==0: l.pop()
    return l
def run_until(cfg,target,maxn=10**7):
    """run from cfg=(st,L,h,R) until PE-equal to target; returns steps or None"""
    st,L,h,R=cfg
    N=len(L)+len(R)+4*maxn if maxn<10**5 else len(L)+len(R)+200000
    # tape array
    pad=100000
    tp=[0]*(pad)+list(reversed(L))+[h]+R+[0]*pad
    pos=pad+len(L)
    tst,tL,th,tR=target
    tLt=trim(tL); tRt=trim(tR)
    for n in range(1,maxn+1):
        r=tp[pos]
        if (st,r) not in TR: return ('HALT',n)
        w,d,s2=TR[(st,r)]; tp[pos]=w; pos+=d; st=s2
        if st==tst and tp[pos]==th:
            # compare
            ok=True
            for i,x in enumerate(tLt):
                if tp[pos-1-i]!=x: ok=False;break
            if ok:
                j=pos-1-len(tLt)
                if any(tp[:j+1]): ok=False
            if ok:
                for i,x in enumerate(tRt):
                    if tp[pos+1+i]!=x: ok=False;break
            if ok:
                j=pos+1+len(tRt)
                if any(tp[j:]): ok=False
            if ok: return n
    return None
