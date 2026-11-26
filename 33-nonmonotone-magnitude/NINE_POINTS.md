# Nine points suffice for nonmonotonic metric magnitude

**Result.** Gomi and Tsuji ask whether any genuine negative-type metric on fewer than 14 points has nonmonotone magnitude. Nine suffice, even with *strict* negative type. Seven of the points are the nonzero vertices of a three-dimensional cube; two substitute for the missing corner. The number nine is an upper bound, not a proved minimum.

For a finite metric space with distance matrix $D$, let $K(t)_{ij}=e^{-tD_{ij}}$. Its magnitude is $M(t)=\mathbf1^T K(t)^{-1}\mathbf1$ whenever the inverse exists. Negative type means $z^TDz\le 0$ for every zero-sum $z$; strict negative type requires strict inequality for nonzero such $z$.

## The metric

Let $V=\{0,1\}^3\setminus\{0\}$ and add two symbols $+,-$. With $|v|$ the number of ones and $h$ the Hamming distance, set
$$
 D(v,w)=2h(v,w),\quad D(v,+)=D(v,-)=2|v|+1,\quad D(+,-)=4 .
$$
The diagonal is zero. These distances obey every triangle inequality. For two cube points and one apex this follows from $||v|-|w||\le h(v,w)\le |v|+|w|$. With two apices and a cube point use $4\le 2(2|v|+1)$, since $|v|\ge1$. Pure cube triangles are Hamming triangles.

Map $v\mapsto(v,v,0)\in\mathbb R^7$ and the apices to $\pm e_7$. Then $D(x,y)=\|x-y\|_2^2$ in those coordinates. Hence for $\sum_i z_i=0$,
$$
 z^TDz=-2\Big\|\sum_i z_i x_i\Big\|_2^2\le0 .
$$
This squared distance, **not** the ordinary Euclidean distance, is the metric here. The kernel is positive definite at every $t>0$: it is the Gaussian kernel on distinct Euclidean points. For a direct proof, its quadratic form (up to the strictly positive Gaussian Fourier normalization) is $\int|\sum_j w_j e^{i \xi\cdot x_j}|^2 e^{-\|\xi\|^2/(4t)}\,d\xi$. If this vanishes, the exponential sum vanishes everywhere; restricting to a line having distinct projected coordinates and taking successive derivatives at zero gives an invertible Vandermonde system.

## Why splitting the corner works

This calculation gives a one-parameter family and explains the decrease. Use the original cube Hamming distance, assign $d(v,\pm)=|v|+s$ and $d(+,-)=4s$, with $0<s\le1$. This is squared Euclidean distance on the seven binary vertices at height zero and the two apices at heights $\pm\sqrt{s}$. The preceding triangle proof works since $4s\le 2+2s$. At $s=1/2$, doubling this metric gives precisely $D$ above.

Let $q=e^{-t}$, $\alpha=e^{-st}$. In the *full* cube similarity matrix, remove the origin to obtain the $7\times7$ principal block $A$, and let $u$ be its deleted column with the diagonal entry omitted. Put $h=1-u^TA^{-1}u$ and $\ell=1-u^TA^{-1}\mathbf1$. The full cube matrix is the tensor cube of $\bigl(\begin{smallmatrix}1&q\\q&1\end{smallmatrix}\bigr)$. Its inverse has origin diagonal $(1-q^2)^{-3}$ and its weighting is constant $(1+q)^{-3}$. Block inversion at the origin therefore gives
$$
 h=(1-q^2)^3,\qquad \ell=(1-q)^3,\qquad
 M_A=\left(\frac{2}{1+q}\right)^3-\frac{\ell^2}{h}.
$$
In the split cube, both new columns on the old seven vertices equal $\alpha u$. Eliminating the seven old coordinates in the weighting equations, the two apex weights are equal; the eigenvalue of their Schur complement on the symmetric axis is $1+\alpha^4-2\alpha^2(1-h)$. The magnitude is consequently
$$
 M_s(t)=M_A+
 \frac{2(1-\alpha+\alpha\ell)^2}{(1-\alpha^2)^2+2\alpha^2 h}.
$$
At small positive $t$, $h=8t^3+O(t^4)$, $\ell=t^3+O(t^4)$, and $M_A=1+3t/2+O(t^2)$. The last numerator and denominator expand respectively as $2s^2t^2(1-st+O(t^2))$ and $4s^2t^2[1+(4/s^2-2s)t+O(t^2)]$. Thus
$$
 M_s(t)=\frac32+\left(\frac32+\frac{s}{2}-\frac{2}{s^2}\right)t+O_s(t^2).
$$
The slope is strictly negative for every $0<s<1$. At $s=1/2$ it equals $-25/4$, hence it is $-25/2$ for the doubled distance $D$. It is the derivative of the analytic extension with limiting value $3/2$, not a derivative obtained by artificially assigning the value 1 at zero.

In fact the slopes are unbounded below as $s\downarrow0$, though the spaces have only nine points and converge to the ordinary cube. The transition occurs at $t\asymp s^2$: substitution of $t=s^2v$ into the exact Schur formula gives
$$
 \lim_{s\downarrow0}M_s(s^2v)=1+\frac1{2+8v}\quad(v>0).
$$
Here the numerator of the excess term is asymptotic to $2s^6v^2$, and the denominator to $4s^6v^2+16s^6v^3$. This scaled profile is not an approximation on which the counterexample depends.

## An exact four-by-four proof of a decrease

The layers of cube weights 1, 2, 3 and the two apices are four orbits of sizes $(3,3,1,2)$. With $q=e^{-t}$ the similarity matrix acts on orbit-constant vectors by
$$
 B(q)=\begin{pmatrix}
 1+2q^4&q^6+2q^2&q^4&2q^3\\
 q^6+2q^2&1+2q^4&q^2&2q^5\\
 3q^4&3q^2&1&2q^7\\
 3q^3&3q^5&q^7&1+q^4
 \end{pmatrix}.
$$
The unique weighting $K(t)^{-1}\mathbf1$ is orbit-constant. By solving this system,
$$
 M(t)=(3,3,1,2)B(q)^{-1}\mathbf1
 =\frac{P(q)}{(1+q)^2(1+q^2)^2 C(q)},
$$
where
$$
\begin{aligned}
P(q)={}&12q^{10}+28q^9+32q^8+32q^7+7q^6-26q^5\\
      &-31q^4-24q^3-27q^2-18q-9,\\
C(q)={}&2q^{10}+4q^8-4q^4-2q^2-1.
\end{aligned}
$$
The quotient at $q=1$ has value $3/2$ and $q$-derivative $25/2$. Consequently
$$
                M(t)=\tfrac32-\tfrac{25}{2}t+O(t^2)
                \qquad(t\downarrow0).
$$
This is the right derivative of the *analytic extension* with limiting value $3/2$; it is not the derivative obtained by assigning the one-point value 1 at zero. In particular $M$ strictly decreases on a nonempty positive-scale interval. The script below independently verifies the bounded-degree rational identity against the full nine-point matrix at 39 distinct rational arguments.

## Strict negative type, with explicit rational checks at two scales

Define $\beta=1-10^{-10}$, $q_0=99/100$ and $\gamma=\log(\beta)/\log(q_0)>0$. Set $D'_{ij}=D_{ij}+\gamma$ when $i\ne j$, keeping the diagonal zero. Every triangle inequality is preserved. On the zero-sum subspace the additional quadratic form is $-\gamma\sum_i z_i^2$, so $D'$ has strict negative type. Its kernel is $e^{-t\gamma}K(t)+(1-e^{-t\gamma})I$, still positive definite.

At $t_1=-\log(q_0)$ the perturbed four-orbit matrix is $B_1=(1-\beta)I+\beta B(q_0)$. At $t_2=2t_1$ it is $B_2=(1-\beta^2)I+\beta^2 B(q_0^2)$. All entries are rational. Direct elimination gives
$$
 \tfrac{141}{100}< (3,3,1,2)B_1^{-1}\mathbf1 <\tfrac{142}{100},
 \qquad
 \tfrac{138}{100}< (3,3,1,2)B_2^{-1}\mathbf1 <\tfrac{140}{100}.
$$
The respective magnitudes are approximately $1.4187004613$ and $1.3882616818$. Thus even the strictly negative-type metric loses magnitude when the scale doubles. No floating-point inference is required.

**Reproduce:** run `python verify_nine.py` in this directory. Only the Python standard library is needed. It constructs the full nine-by-nine distance and similarity matrices independently of the orbit formula, checks every triangle and squared-distance identity, solves both rational systems, checks both weightings by multiplication, certifies the displayed inequalities, and checks the unperturbed rational identity and slope. The accompanying `MAGNITUDE.md` proves two infinite-scale extensions.

## Literature status and limits

[Gomi and Tsuji, introduction](https://arxiv.org/html/2608.15720v1) explicitly identify the smaller-than-14 question, and show all at-most-three-point negative-type semimetrics are monotone. Their four-point counterexamples lack triangle inequalities. [Pendyala, Theorem 4.1](https://arxiv.org/html/2610.13958v1) gives the 14-point strict-negative-type example; it uses a different construction. Earlier nonmonotone graph examples without the negative-type hypothesis, such as the one in [Leinster, Example 2.2.7](https://ems.press/journals/dm/articles/8965346), do not give smaller examples in the target class. Targeted searches for smaller metric counterexamples, the split-cube construction, and follow-ups to both 2026 papers located no matching earlier result. This is evidence of priority, not a guarantee.

The located lower and upper bounds for the minimum order of a genuine negative-type counterexample are therefore **4 and 9**. A failure with four through eight points is not excluded. A broad numerical search is not a monotonicity proof.
