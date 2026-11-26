# Why merely averaging the balanced drift does not remove the balance hypothesis

In the convex-kernel proof one might hope that rare coupons are preferentially still missing, so that replacing the actual conditional drift by the balanced drift is always justified *after averaging*. The assertion is false even for the order-two kernel.

Take $q=4,s=2,n=8$. Partition the coupons into a pair and two triples. The supported packages are the pair (probability $191/768$) and the three edges of each triple (each of the six has probability $577/4608$). Denote the singleton marginals by $p_i$. After two draws let $C$ be the covered set and $Y=|C|/2$. The surplus of the actual drift over the balanced drift is $\tfrac12\sum_{i\notin C}(p_i-1/4)$. The chord weight $g(Y)=b_2(Y+1)-b_2(Y)$ is well defined since $Y\le2$. Directly summing over the 49 ordered package pairs gives
$$
 \mathbb E\!\left[g(Y)\,\tfrac12\sum_{i\notin C}(p_i-1/4)\right]
 =\frac{2854979}{856141332480}>0.
$$
Thus even the averaged sign of the drift error need not favor the conjecture. This is *not* a counterexample to Long's comparison: the chord itself also has slack. A continuation would have to control drift error by that slack, or compare to a nonuniform block reference before equalizing its block probabilities. The counterpart of the former in the balanced proof is the explicit partial-overlap deficit. The file verify-obstruction.py uses only rational arithmetic.
