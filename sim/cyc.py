from am import *
def Lam(l,N):
    if l==0: return [(N%2,2)]
    return [(N%2,2**l+2*((N+2)//4))]+Lam(l-1,N//2)
def O(l): return [(1,2**j) for j in range(l,0,-1)]
def preL(l,a): return O(l) if a==0 else Lam(l,2*a-1)
def ident(L):
    for l in range(1,20):
        if L==O(l): return (l,0)
        if len(L)==l+1:
            for a in range(1,2**l):
                if L==Lam(l,2*a-1): return (l,a)
    return None
S=(0,('cl',[2]),1,[(1,2)])
i=0; last=None; R=None; worst=[]
import sys
MAXL=int(sys.argv[1])
while True:
    k,C,m,L=S
    if k+1+m==2 and L and L[0][0]==1 and C[0]=='cl':
        la=ident(L); V=val(C[1])
        if la is None: print('NOSHAPE',S); break
        l,a=la
        E=2**l+a+1
        if last: 
            pl,pa,pV,pE,pi=last
            print(f"l={pl} a={pa} V={pV} E={pE} steps={i-pi} R={R} V'={V} ratio={pV/pE:.3f}") if pl<=4 or pa==0 else None
            assert i-pi==pE+1, 'E mismatch'
            worst.append((pV/pE,pl,pa, R/pE))
        last=(l,a,V,E,i); R=None
        if l>=MAXL: break
    S,tag=astep(S); i+=1
    if tag=='R': R=i-last[4]-1   # phases after ABS step until realign (1-indexed count)
worst.sort(); print('max V/E',worst[-3:]); print('max R/E',max(w[3] for w in worst))
