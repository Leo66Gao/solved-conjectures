def parts(s):
    if not s: yield []; return
    x,*rest=s
    for P in parts(rest):
        yield [{x}]+P
        for i in range(len(P)): yield P[:i]+[P[i]|{x}]+P[i+1:]
allparts=list(parts(['2','4','p','2p','4p']))
assert len(allparts)==52
splits=[{'2'},{'2','4'},{'p'},{'2','p','2p'}]
inactive=[{'2'},{'4'},{'2','2p'},{'4','4p'}]
good=[P for P in allparts if all(any(B&S and not B<=S for B in P) for S in splits) and sum(B not in inactive for B in P)>=3]
assert len(good)==3
for P in good: print(' | '.join(','.join(sorted(B)) for B in P))
