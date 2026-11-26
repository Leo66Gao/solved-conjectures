"""Direct independent check of the infinitely replicated local obstruction to a bound of eight."""
import itertools
N=5
def adj(v):
    i,x,y=v
    for a,b in ((0,0),(1,0),(0,1)):
        c=1-2*i
        yield(1-i,(x+c*a)%N,(y+c*b)%N)
def cycles(L):
    start=(0,0,0);path=[start];active={start}
    def run():
        if len(path)==L:
            if start in adj(path[-1]):yield tuple(path)
            return
        for v in adj(path[-1]):
            if v not in active:
                active.add(v);path.append(v);yield from run();path.pop();active.remove(v)
    yield from run()
for L in (4,8,16):
    a=list(cycles(L));print(L,len(a)//2,'unoriented cycles through 0')
    assert bool(a)==(L==16)
