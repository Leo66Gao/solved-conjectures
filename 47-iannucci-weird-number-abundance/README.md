# Iannucci's abundance conjecture for weird numbers

**Leo Gao** · AI-assisted research

This gives an elementary proof of [Iannucci’s 2015 conjecture, §III, equation (6)](https://iosrjournals.org/iosr-jm/papers/Vol11-issue3/Version-3/K0113386130.pdf). For a weird number of the form $n=2^kpq$, where $k\ge 1$ and $p<q$ are odd primes, write $M=2^{k+1}-1$. Then

$$M<\sigma(n)-2n<\frac{(M+1)(M+2)}3.$$

A failure of the bound would force a progression of least residues to stay in a short interval. Its common difference can only be one of eight small integers; each gives a contradiction or an explicit proper-divisor representation. In this family, 70 uniquely maximizes the abundancy index. The [infinitude and parity questions of Erdős #470](https://www.erdosproblems.com/470) are not settled here.

- [Paper (PDF)](paper.pdf) · [LaTeX](paper.tex) · [Proof in Markdown](theorem.md)
- [Optional exact diagnostic](verify.py): run `python3 verify.py` to reproduce the published counts through $k=8$ by direct subset sums and test the auxiliary certificate on a larger finite domain. See [recorded output](verification.txt). The proof does not depend on these calculations.

This is a research manuscript, not an assertion of peer review or confirmed historical priority.
