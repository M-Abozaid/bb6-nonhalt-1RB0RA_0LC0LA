# run machine from blank; print parsed checkpoints that are pre-ABS (B1=2, s1=1, clean)
import sys
from tm import TR
from parse import parse
from am import *
N=int(sys.argv[1])
pad=200000
tp=[0]*(2*pad); pos=pad; st='A'
for n in range(1,N+1):
    r=tp[pos]
    if (st,r) not in TR: print('HALT',n); break
    w,d,s2=TR[(st,r)]; tp[pos]=w; pos+=d; st=s2
    if st=='B' and tp[pos]==1 and tp[pos+1]==1 and tp[pos+2]==1 and tp[pos-1]==1:
        lo=pos-1
        while lo>0 and any(tp[lo-40:lo]): lo-=40
        hi=pos
        while any(tp[hi:hi+40]): hi+=40
        L=tp[lo:pos][::-1]; R=tp[pos+1:hi]
        ps=parse(L,R)
        for S in ps:
            k,C,m,Ld=S
            if k+1+m==2 and Ld and Ld[0][0]==1 and C[0]=='cl':
                print(n,S); break
