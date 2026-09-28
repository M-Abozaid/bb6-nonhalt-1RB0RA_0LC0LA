# simulate with Lean list semantics, print config after N steps as Lean term
import sys
from tm import TR
N=int(sys.argv[1])
st,L,h,R='A',[],0,[]
for n in range(N):
    w,d,s2=TR[(st,h)]
    if d==1:
        L=[w]+L; h=R[0] if R else 0; R=R[1:]
    else:
        R=[w]+R; h=L[0] if L else 0; L=L[1:]
    st=s2
b=lambda x:'true' if x else 'false'
def rl(l):
    # run-length: list of (value,count)
    return '['+', '.join(b(x) for x in l)+']'
print(st,len(L),len(R))
print('L',''.join('1' if x else '.' for x in L))
print('R',''.join('1' if x else '.' for x in R))
open(sys.argv[2],'w').write(f"⟨.{st}, {rl(L)}, {b(h)}, {rl(R)}⟩")
