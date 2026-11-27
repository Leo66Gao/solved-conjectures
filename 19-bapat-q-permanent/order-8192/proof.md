# Certificate justification

## 1. The matrix and endpoint identity

For an n-by-n matrix A, define P_q(A)=sum_sigma q^inv(sigma) prod_i A[i,sigma(i)]. For real row vectors v_i, H=VV^T, L_i(z)=v_i.z, p=prod_i L_i, and

    F_ab = sum_{i<j} (v_ia v_jb - v_ib v_ja) prod_{k != i,j} L_k.

For f=sum_alpha f_alpha z^alpha put ||f||_F^2=sum_alpha alpha! |f_alpha|^2. The factorial inner product of two products of linear forms equals the permanent of their pairwise inner-product matrix (expand the differential operator of one product applied to the other). In particular per(H)=||p||_F^2. Expanding sum_ab ||F_ab||_F^2 by the exterior-product identity gives, for each permutation, its product times the number of ascending pairs minus the number of descending pairs. Thus, with C=binom(n,2),

    2P'_1(H) = C per(H) - sum_{a<b} ||F_ab||_F^2.             (1)

This identity applies to any real rank, including the lifted Gram factor below. It is also tested on six integer matrices against exact permutation enumeration in `verify.py` (121032 permutation terms). For the independent monomial test the update on appending v with L=v.z is p_new=L p and F_ab,new=L F_ab+v_b partial_a p-v_a partial_b p. This follows by separating pairs whose second index is the newly appended row.

Set m=32, N=256, n=mN=8192, s=49791/50000, S=10^12. Define u_j=(2j+1)/(2N) for 0<=j<N, a_j^2=2s^2 u_j^2/(1-u_j^2), theta_k=(2k+1)pi/m, 0<=k<m. Reference rows are

    v_jk=(cos(theta_k),sin(theta_k),a_j/sqrt(2)).

Round each coordinate at scale S using the deterministic procedure in `build` in `verify.py`. The trigonometric bounds follow from the alternating arctangent series, Machin's pi formula and alternating cosine Taylor series on the first quadrant; integer square-root intervals bound the heights. The midpoint of each rational interval is rounded to the nearest integer at scale S and the error of each endpoint is checked to be at most 1/S. Other quadrants are obtained by exact rotations. Sort the resulting integer rows W_i=(x_i,y_i,b_i) stably by increasing rational b_i*x_i/(x_i^2+y_i^2), initially listed with j outermost, k innermost. Apply the same permutation to the reference rows. The bundled JSON is checked against the reconstructed W. The required counterexample is

    A=W W^T+I_n.

It is real, symmetric, integer, positive definite since x^TAx=||W^Tx||^2+||x||^2, and non-diagonal (two distinct neighboring angular rows in the same ring have positive inner product, checked on the integer plane coordinates). No giant identity-perturbation scale is necessary.

## 2. Full product-polynomial upper bound, exploiting rings

The factorial norm is invariant under unitary changes of variables. For example, this follows by expressing it as E|f(G)|^2 for a standard complex Gaussian vector G, whose distribution is unitary invariant. Let z0=(1,i,0)/sqrt(2), conjugate z0, and e3 be the unitary basis and use coordinates x,y,w in it. Each linear factor in ring j becomes 2^(-1/2)(x e^(i theta_k)+y e^(-i theta_k)+a_j w).

With q=e^(i theta_k), q^m=-1. Multiplying each factor (without 2^(-1/2)) by q gives x q^2+a_j w q+y; prod_k q=1. Factoring the quadratic with roots r1,r2 gives ring product x^m(r1^m+1)(r2^m+1)=x^m+y^m+x^m(r1^m+r2^m). The resulting identity is polynomial and extends to x=0. Root power sums obey the recursion S_l=t S_(l-1)-r S_(l-2), with S_0=2, S_1=t, where t=-a_j w and r=xy after absorbing powers of x. Expanding the recurrence (or induction) yields coefficients (-1)^h c_h, c_h=m/(m-h)*binom(m-h,h). Since m is a multiple of four, replacing y by -y leaves y^m unchanged and makes every coefficient nonnegative. Hence the transformed ring polynomial is

    Q_j = x^m+y^m+sum_{h=0}^{m/2} c_h (a_j^2)^(m/2-h) (xy)^h w^(m-2h).

Therefore per(VV^T)=2^(-n)||prod_j Q_j||_F^2 exactly. No trigonometric approximation enters the norm of the reference frame. Note that the reference row permutation does not change the permanent.

All monomials satisfy alpha_x-alpha_y=0 mod m. For a product of t rings, degree d=tm, store b_alpha=c_alpha sqrt(alpha!/d!) where c_alpha is its ordinary coefficient. When multiplying by the next Q with coefficient q_beta, update

    b_new[alpha+beta] += b_alpha q_beta
        * sqrt(prod_l (alpha_l+beta_l)!/alpha_l!)
        / sqrt((d+m)!/d!).

The normalized squared norm is sum_alpha b_alpha^2. At the final degree there are 1049089 allowed slots, instead of 33566721 unrestricted trivariate monomials. Both C++ programs evaluate all allowed slots, without discarding small coefficients. For each k, the exact integer floor of 2^40 sqrt(k) is computed and its two bounding inequalities are checked. Products of lower sqrt endpoints give the denominator lower bound, products of upper endpoints give numerator upper bounds. Every ring coefficient is nonnegative; c_h are exact integers, a_j^2 is rational, and the multiplications and additions are monotone on nonnegative numbers. Directed rounding thus propagates an upper bound inductively on every normalized coefficient. The final sum is rounded upwards to a rational U with denominator 2^40.

The integer kernel represents positive dyadics as m0*2^e, with 2^55<=m0<2^56. Addition aligns exponents with ceiling shifts and normalizes upwards. Products are computed in 128-bit integers and rounded by shifts (up for numerator, down for denominator); reciprocals are rounded upwards by integer ceiling division. Exact integer input conversion is directed as needed. The exponents have ample range for these fixed parameters: sqrt factors lie between 1/2 and 128, a_j^2 between 2^-20 and 2^10, and each ring multiplication scales any summand by a product of at most 32 such roots, at most 16 powers of a_j^2, one reciprocal denominator product, and an integer coefficient <2^64. Even allowing a factor 2 for each mantissa rounding and sums over all allowed slots, fewer than 256 stages change exponents by far less than 10^6. All mantissa intermediates fit the specified 64- or 128-bit types. The interval kernel instead uses explicit directed rounding with runtime arithmetic tests and exact integer sqrt enclosures. All final sign decisions use Python fractions.

## 3. Exact exterior lower bound for the ACTUAL rounded rows

Let Hhat=(W/S)(W/S)^T, and write phat,Fhat for its polynomials. In the unitary coordinates used above, evaluations at z0 and conjugate z0 select distinct pure monomial coefficients of degree n-2. Their contributions to the factorial norm are disjoint. Because the rows are real,

    sum_ab ||Fhat_ab||_F^2 >= 2(n-2)! |phat(z0)|^2 E,
    E = sum_ab |Fhat_ab(z0)/phat(z0)|^2.

Every plane radius is at least 1-2/S, so |phat(z0)|^2 >= 2^(-n)(1-2/S)^(2n) >= 2^(-n)(1-4n/S) by Bernoulli's inequality.

E is calculated exactly, not sampled. Put D=lcm_i(x_i^2+y_i^2) and let U_i = W_i (x_i-i y_i) D/(x_i^2+y_i^2), a Gaussian integer vector. Then the row divided by its linear evaluation at z0 equals sqrt(2) U_i/D. Each exterior quotient is 2/D^2 times sum_{i<j}(U_ia U_jb-U_ib U_ja). A prefix sum computes these three Gaussian integer sums in linear time. Taking squared absolute values gives E as an exact fraction. Thus the exterior contribution divided by C n! 2^(-n) is at least

    Nlower = 2(1-4n/S) E / (C n(n-1)).

## 4. Rigorous rounding and positive-definite lift

For any real vector v and homogeneous polynomial f of degree d, unitary invariance and rotation of v onto the first coordinate give

    ||v|| ||f||_F <= ||(v.z) f||_F <= sqrt(d+1) ||v|| ||f||_F.

Indeed each monomial's squared factorial weight is multiplied by alpha_1+1, between 1 and d+1. Replacing one reference row v by its rounded version changes the product norm by at most a factor 1+delta, delta=2 ceil(sqrt(n))/S: the row error norm is at most 2/S and the original row norm at least 1. Iterating over all n rows and squaring gives per(Hhat)<=per(VV^T)(1+delta)^(2n)<=per(VV^T)/(1-2n delta), since the binomial expansion is bounded by the geometric series for 2n delta<1.

For A/S^2=Hhat+I/S^2, expanding the permanent along the added diagonal entries gives a sum of principal permanents of Hhat. The lower multiplication inequality and rounded row norms squared >=1/2 imply per(Hhat[complement J])<=2^|J| per(Hhat). Therefore the lift increases the permanent by at most a factor (1+2/S^2)^n<=1/(1-2n/S^2). Combining with the coefficient norm upper bound gives

    per(A/S^2)/(n! 2^(-n)) <= Pupper = U/[(1-2n delta)(1-2n/S^2)].

A real Gram factor for A/S^2 consists of the rows (W_i/S,e_i/S). The wedge polynomials for the first three coordinates, restricted by setting the last n variables to zero, are exactly the three Fhat polynomials. Norm contributions from the other monomials and wedge components are nonnegative. Consequently (1) implies

    2P'_1(A/S^2)/(C n! 2^(-n)) <= Pupper - Nlower.

The final Python check proves by exact rational comparison Nlower-Pupper>1/4000. In particular P'_1(A)<0, since positive scalar multiplication preserves the derivative sign.

## 5. Explicit rational comparison strictly inside the interval

The verifier also checks max_i ||W_i||^2 < 1023 S^2. All entries of A/S^2 consequently have absolute value <1024. For 0<=q<=1, direct differentiation of the defining finite permutation sum gives |P''_q(A/S^2)| <= n! C^2 1024^n (terms of inversion degree <2 have zero second derivative). The derivative upper bound just obtained is -C n! 2^(-n)/8000. Set

    h=1/(16000 C 2048^n),  q1=1-h,  q2=1-h/2.

The mean value inequality proves the derivative remains negative on [1-h,1], so P_q1(A)>P_q2(A) with both rational q values strictly inside [-1,1].

This completes the sign certificate for the explicit matrix, conditional only on the stated elementary identities and the finite arithmetic computations in the verifier. No direct full permanent or full derivative is claimed, and no minimality or independent external review is claimed.
