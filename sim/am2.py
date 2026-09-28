# Nat-valued abstract model mirroring the Lean definitions (M8/R3Abs.lean)
from am import Sr, Lu, Rr, lad, val, inc, linc, lowok
def dig(v):
    ds=[]
    while v: ds.append(v%3); v//=3
    return ds
def shv(v):
    if v==0: return ('cl',0)
    if v%3==0:
        C=shv(v//3); assert C[0]=='lone'; return ('lone',[0]+C[1],C[2])
    if v%3==1: return ('lone',[2],v//3)
    return ('lone',[0],v//3)
def ctape(C):
    if C[0]=='cl': return Sr(dig(C[1]))
    return Sr(C[1])+[1]+Sr(dig(C[2]))
def cph(C):
    if C[0]=='cl': return 0,('cl',C[1]+1)
    lo,hv=C[1],C[2]
    if lowok(lo): return 0,('lone',inc(lo),hv)
    if lo: return 1,('cl',3**(len(lo)-1)*(hv+1))
    return 0,shv(hv+2)
def absStep(C,L2):
    assert C[0]=='cl' and L2 and L2[0][0]==0
    b=L2[0][1]; rest=L2[1:]; W=C[1]+2; q=W//3
    if W%3==0: return (1,shv(q),b-1,rest)
    if W%3==2: return (1,('lone',[],q),b-1,rest)
    return (0,shv(q+1),b,rest)
def astep(S):
    k,C,m,L=S
    p,L2=linc(k+1+m,L)
    if p==0: return absStep(C,L2)
    k2,C2=cph(C); return (k2,C2,p-1,L2)
def render(S):
    k,C,m,L=S
    return ('B',[1]+Rr*k+ctape(C),1,[1,1]+Lu*m+lad(L))
if __name__=='__main__':
    import sys
    from tm import run_until
    S=(0,('cl',17),1,[(1,16),(1,8),(1,4),(1,2)])   # pre-ABS (4,0) at t=46083
    tot=0
    for i in range(int(sys.argv[1])):
        S2=astep(S)
        n=run_until(render(S),render(S2),maxn=5*10**6)
        if not isinstance(n,int): print('FAIL',i,S,S2,n); break
        tot+=n; S=S2
    print('ok',i+1,'steps',46083+tot, S[:3], S[3][:3])
