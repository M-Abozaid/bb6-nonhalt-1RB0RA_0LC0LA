from am import *
def todig(V):
    ds=[]
    while V: ds.append(V%3); V//=3
    return ds
def epoch(V,E):
    """counter-only epoch from pre-ABS clean value V. returns (rho, V') or None"""
    W=inc(inc(todig(V)))
    d0,r=W[0],W[1:]
    if d0==0: C=sh(r)
    elif d0==2: C=('lone',[],r)
    else: C=sh(inc(r))
    rho=None
    for i in range(E):
        k,C=cph(C)
        if k==1: rho=i
    if C[0]!='cl' or rho is None: return None
    return rho,val(C[1])
import sys
E0,E1=int(sys.argv[1]),int(sys.argv[2])
for E in range(E0,E1):
    bad=None; mx=0
    for V in range(1,2*E):
        r=epoch(V,E)
        ok = r is not None and r[0]<=E-2
        if not ok: bad=V; break
        if 5*V<=6*E: mx=max(mx,r[1])
    print(E,'first bad V',bad,'maxV\' for 5V<=6E:',mx,'6(E+1)/5=',6*(E+1)/5)
