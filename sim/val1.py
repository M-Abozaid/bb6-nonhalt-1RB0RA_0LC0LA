# validate abstract astep against real machine: render(S) ->run-> render(astep S)
import sys
from am import *
from tm import run_until
S=(0,('cl',[2]),1,[(1,2)])
nsteps=int(sys.argv[1]); tot=0; tags={}
for i in range(nsteps):
    S2,tag=astep(S)
    n=run_until(render(S),render(S2),maxn=5*10**6)
    if not isinstance(n,int): print('FAIL',i,S,S2,n); break
    tot+=n; tags[tag]=tags.get(tag,0)+1
    S=S2
print('ok',nsteps,'machine steps',tot+323,tags)
print(S)
