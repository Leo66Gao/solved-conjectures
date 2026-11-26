# Fractional planks in equal-normal planes
**Leo Gao · AI-assisted · private.**

Main result: every convex set packed in an equal-normal section of the three-cube, at every offset, has a \(2/3\)-mass measure matching in the unit-cube convention (mass \(4/3\) in \([-1,1]^3\)). A translated triangular template provides the law. The constant is sharp across those planes. This does not settle arbitrary planar orientations or arbitrary spatial bodies.

- [All-offset manuscript](all-equal-offsets.pdf), [LaTeX source](all-equal-offsets.tex), and [text proof](all-equal-offsets.md).
- [Symbolic certificate](verify-offset-symbolic.py) and [output](offset-symbolic-checks.txt). Requires SymPy.
- [Independent Bernstein certificate](verify-offset-bernstein.py) and [output](offset-bernstein-checks.txt). Python standard library only.
- [Exact geometric stress test](verify-offset-construction.py) and [output](offset-construction-checks.txt). It checked 28,672 exhaustive cases at seven rational offsets plus 4,000 rational seeded cases. The geometric tests audit the continuum proof; they are not a proof by sampling.

Earlier in this run: the [central plane proof and stability supplement](central-hexagon.pdf) give a strict (unquantified) uniform improvement near the central equal-normal plane, including small perturbations of the normal. A separate [planar-sections note](planar-sections.md) records exact complete-section capacity, a quantitative Hausdorff stability bound, a near-dominant-normal class, and a cited universal planar lower bound. Priority and external peer review are not established.

[Strictness supplement](strict-equal-offsets.pdf) ([source](strict-equal-offsets.md)): the capacity is strictly above \(2/3\) at every interior offset, with uniform improvement on each compact subinterval of \((1,2)\). Only the two simplex sections attain equality in the equal-normal class. An elementary extra matching handles the one exceptional contact kite where enlarging the original triangular motif need not work.
