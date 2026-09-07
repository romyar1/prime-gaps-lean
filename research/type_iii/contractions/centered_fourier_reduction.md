# Centering the actual Type III Fourier four-cycle

This note gives an exact reduction that keeps all four fixed indices and
the nonlinear physical substitution. It removes a contribution of size
at most \(32p^3\), using exact finite-sum identities and elementary
inequalities only. The remaining centered four-factor sum is still an
unproved cancellation problem.

The conventions for \(f=\mathrm{kl}_3\), \(C_c\), \(S_2\), and the
complete Gram identity are in
[common_column_contraction.md](common_column_contraction.md).
All Fourier transforms in the main statement use the positive,
unnormalized convention of
[TypeIIILocal.lean](../../../formal/TypeIIILocal.lean).
The current exact spectrum formula is in
[TypeIIIExactSpectrum.lean](../../../formal/TypeIIIExactSpectrum.lean);
it does not evaluate the cancellation isolated below.

## 1. The actual physical fibers

Let \(p\) be prime, \(G=\mathbf F_p^\times\), \(N=p-1\), and
\(\kappa=1+p^{-1}+p^{-2}\). Fix
\(\alpha,m,m',n,n'\in G\), with \(m\ne m'\) and \(n\ne n'\), and put

\[
 a=m/m',\qquad b=n/n',\qquad
 A=\frac{\alpha y}{mx^2},\qquad
 B=\frac{\alpha x}{ny^2},\qquad
 \lambda=\frac{\alpha^3}{m^2n}.
 \tag{1}
\]

Thus \(a,b\ne1\), and every \(A,B\) argument occurring physically is a
unit. Write \(C(A,B)=C_1(A,B)\), and define

\[
 P_A(B)=C(A,B)\overline{C(aA,B)}.
 \tag{2}
\]

The actual four-cycle, on \(x,y\ne0\), is exactly

\[
 P_A(B)\overline{P_A(bB)}.
 \tag{3}
\]

Solving (1) for a physical point above \(A,B\) gives

\[
 x^3=\frac{\lambda}{A^2B},\qquad
 y=\frac m\alpha A x^2.
 \tag{4}
\]

For physical Fourier frequencies \(h,k\in\mathbf F_p\), retain the
following fiber weight:

\[
 \Xi_{h,k}(A,B)=
 \sum_{\substack{x\in G\\x^3=\lambda/(A^2B)}}
       \psi\!\left(hx+k\frac m\alpha A x^2\right).
 \tag{5}
\]

Each \(x\) in (5) determines exactly one \(y\) by (4), and direct
substitution recovers both equations in (1). Therefore the actual
Fourier coefficient is

\[
 \boxed{\;
 \widehat W(h,k)=
 \sum_{A,B\in G}\Xi_{h,k}(A,B)
          P_A(B)\overline{P_A(bB)}.
 \;}
 \tag{6}
\]

There is no Jacobian, factor of \(p\), or normalization factor in (6).
The axes in physical space contribute zero, as specified by the actual
kernel definition.

The map \(x\mapsto x^3\) on \(G\) has fibers of size either zero or
\(d=\gcd(3,N)\). Consequently

\[
 |\Xi_{h,k}(A,B)|\le d\le3.
 \tag{7}
\]

If \(d=1\), then \(\Xi_{0,0}=1\). When \(d=3\), even at the origin
the weight must be retained: it is zero or three according to the
cubic fiber condition. This distinction is essential.

## 2. The part evaluated by common-column contraction

The complete Gram identity, with rows \(A,aA\), gives

\[
 \begin{aligned}
 G_A:=\sum_{B\in G}P_A(B)
 &=-\kappa\bigl(p+U_A\overline{U_{aA}}\bigr),\\
 U_A&=F_1(A)=S_2(-A)-p^{-1}.
 \end{aligned}
 \tag{8}
\]

Here \(a\ne1\) ensures that the \(p^2\) diagonal Gram term is absent.
Define the exact mean and its centered remainder by

\[
 \mu_A=N^{-1}G_A,\qquad Q_A(B)=P_A(B)-\mu_A.
 \tag{9}
\]

In particular \(\sum_B Q_A(B)=0\). Expanding the two factors in (6),
before applying any inequality, gives

\[
 \boxed{\;
 \widehat W(h,k)=\mathcal S_{h,k}(a,b)+E_{h,k},
 \qquad
 \mathcal S_{h,k}(a,b)
   =\sum_{A,B\in G}\Xi_{h,k}(A,B)
                        Q_A(B)\overline{Q_A(bB)},
 \;}
 \tag{10}
\]

where the full correction is

\[
 E_{h,k}=\sum_{A,B\in G}\Xi_{h,k}(A,B)
       \left(
        \mu_A\overline{P_A(bB)}
        +\overline{\mu_A}P_A(B)-|\mu_A|^2
       \right).
 \tag{11}
\]

This is a contraction onto the constant column function. It does not
discard either of the fixed ratios \(a,b\), and does not replace a
physical sum by an unweighted sum.

## 3. Uniform \(32p^3\) error with no Weil input

All bounds in this section follow from the exact Gram identities.
First,

\[
 \sum_{A\in G}|U_A|^2=p(p-1)-\kappa\le pN.
 \tag{12}
\]

One way to obtain the inequality alone is to write \(U=H\psi\), where
\(H_{A,t}=f(At)\), and use \(HH^*=pI-\kappa J\).
For the exact equality, expand \(U_A=S_2(-A)-p^{-1}\); the exact
identities \(\sum_A S_2(-A)=1\) and
\(\sum_A|S_2(-A)|^2=p^2-p-1\) give (12).

By (8), the triangle inequality, and Cauchy--Schwarz applied to the
permutation \(A\mapsto aA\),

\[
 \begin{aligned}
 \sum_A|\mu_A|
 &\le \kappa p+\frac{\kappa}{N}
                         \sum_A|U_AU_{aA}|\\
 &\le \kappa p+\frac{\kappa}{N}\sum_A|U_A|^2
 \le2\kappa p.
 \end{aligned}
 \tag{13}
\]

The row Gram identity also gives

\[
 \sum_B|C(A,B)|^2\le p^2,\qquad
 \sum_B|P_A(B)|\le p^2,\qquad
 |\mu_A|\le p^2/N.
 \tag{14}
\]

The second inequality in (14) is Cauchy--Schwarz on the two rows;
the last follows by taking the absolute value of their average.
Now apply (7), (13), and (14) to the exact correction (11):

\[
 \begin{aligned}
 |E_{h,k}|
 &\le 2d p^2\sum_A|\mu_A|
                +dN\sum_A|\mu_A|^2\\
 &\le3d p^2\sum_A|\mu_A|
 \le6d\kappa p^3
 \le18\kappa p^3\\
 &\le\frac{63}{2}p^3<32p^3.
 \end{aligned}
 \tag{15}
\]

The last step uses \(p\ge2\) and \(\kappa\le7/4\).
No bound for an individual \(S_2(t)\), no Deligne or Weil estimate,
and no exceptional Fourier hypothesis enters this argument.

In particular, a finite-exceptional \(O(p^3)\), \(O(p^{7/2})\) bound
for \(\widehat W\) is equivalent, after increasing its absolute
constant by at most \(32\), to the corresponding bound for
\(\mathcal S\) in (10), with the same exceptional set. The bounded
centering error cannot hide a \(p^4\) origin term.

## 4. A sharper origin correction from elementary fourth moments

When \(d=1\) and \(h=k=0\), the zero means in (9) eliminate both mixed
terms. Formula (11) becomes exactly

\[
 E_{0,0}=N\sum_A|\mu_A|^2
 =\frac{\kappa^2}{N}\sum_A
       \bigl|p+U_A\overline{U_{aA}}\bigr|^2.
 \tag{16}
\]

This term is nonnegative. It is \(O(p^2)\), still without a
pointwise Kloosterman estimate. Here is a finite-sum proof.

For this auxiliary calculation only, use the negative additive Fourier
convention \( \mathcal Fg(\xi)=\sum_t g(t)\psi(-\xi t)\).
Expanding the square of \(S_2\) gives

\[
 \mathcal F(S_2^2)(\xi)=
 p\!\!\sum_{\substack{u,v\in G\\u^{-1}+v^{-1}=\xi}}\!\!\psi(u+v)
 =
 \begin{cases}
 pN,&\xi=0,\\
 p\left[\psi(2/\xi)S_2(\xi^{-2})-1\right],&\xi\ne0.
 \end{cases}
 \tag{17}
\]

For \(\xi=0\), set \(v=-u\). For \(\xi\ne0\), the substitution
\(w=\xi u-1\) gives

\[
 u=(w+1)/\xi,\qquad v=(w^{-1}+1)/\xi,\qquad w\ne0,-1.
\]

Restoring and then subtracting \(w=-1\) yields the second line of
(17), including its minus-one correction.

Parseval, \(|z-1|^2\le2|z|^2+2\), and at most two preimages under the
square map give

\[
 \begin{aligned}
 \sum_{t\in\mathbf F_p}|S_2(t)|^4
 &\le p\left[N^2+2N+
                2\sum_{\xi\in G}|S_2(\xi^{-2})|^2\right]\\
 &\le p\left[N^2+2N+4(p^2-p-1)\right]
 \le5p^3.
 \end{aligned}
 \tag{18}
\]

The second moment used here is the exact rank-two unit orthogonality
identity, not a scalar estimate. The argument includes characteristic
two.

By the finite \(L^4\) triangle inequality,

\[
 \left(\sum_{A\in G}|U_A|^4\right)^{1/4}
 \le(5p^3)^{1/4}+N^{1/4}/p
 \le2p^{3/4},
 \qquad
 \sum_A|U_A|^4\le16p^3.
 \tag{19}
\]

The last inequality follows from \(5^{1/4}\le3/2\),
\(N\le p\), and \(p^{-3/2}\le1/2\). Finally, (16), the inequality
\(|p+z|^2\le2p^2+2|z|^2\), and Cauchy--Schwarz under
\(A\mapsto aA\) give

\[
 0\le E_{0,0}
 \le2\kappa^2p^2+\frac{32\kappa^2p^3}{N}
 \le66\kappa^2p^2
 \le203p^2.
 \tag{20}
\]

No claim that (16) holds for the weighted cubic origin \(d=3\) is
made. The uniform estimate (15) applies there.

## 5. Why the matrix norm does not finish the centered estimate

After fixing \(A\), the remaining sum in (10) is a weighted
multiplicative autocorrelation of the centered row-pair product
\(Q_A\). The complete contraction of two \(C\) factors determines its
constant column component, which has now been removed. Applying
\(C=HDH^*\) to a remaining weighted common-column sum inserts
\(H^*\operatorname{diag}(w)H\), not \(H^*H\); the extra two fixed
correlation factors and the physical weight are part of \(w\).
Replacing this inserted operator by its unweighted Gram value would
change the sum.

The bound \(\|C\|_{2\to2}\le p\) alone is insufficient even when the
same nonlinear torus substitution and fixed distinct row and column
ratios are retained. For example, label \(G\) by discrete logarithms
\(i,j\in\mathbf Z/N\mathbf Z\), and take the artificial matrix

\[
 M_{i,j}=\frac{p}{\sqrt N}\exp(2\pi i\,ij/N).
 \tag{21}
\]

Its norm is \(p\), and its entries have size \(p/\sqrt N\le\sqrt{2p}\).
For nonzero shifts \(r,s\), the corresponding four-cycle is the
constant

\[
 M_{i,j}\overline{M_{i+r,j}}\,
 M_{i+r,j+s}\overline{M_{i,j+s}}
       =\frac{p^4}{N^2}\exp(2\pi i\,rs/N).
 \tag{22}
\]

The nonlinear physical pullback therefore has origin coefficient of
absolute value exactly \(p^4\). The fixed ratios are the units with
discrete logarithms \(r,s\), so they are both distinct from one.
This matrix is not the actual Kloosterman correlation and is not a
counterexample to the desired proposition. It shows precisely why an
unpulled operator norm and entry bound cannot imply the claimed
individual Fourier estimate.

The usable reduction for the actual sum is (10)--(15). Cancellation in
its centered term must use more of the actual correlation than those
matrix norm bounds.

## 6. Selected exact validation

[centered_fourier_exact.py](centered_fourier_exact.py)
uses integer cyclotomic coefficient vectors, with the original
two-unit definition of \(f\). The fixed instances are:

| \(p\) | \(\alpha,m,m',n,n'\) | \(a,b\) | Cubic fiber maximum |
|---:|:---|:---|---:|
| 3 | \(1,1,2,1,2\) | \(2,2\) | 1 |
| 5 | \(2,1,2,1,3\) | \(3,2\) | 1 |
| 7 | \(3,2,3,1,2\) | \(3,4\) | 3 |

For each instance, physical frequencies \((0,0),(1,0),(1,2)\) were
checked directly. All nine physical fiber identities (6), all nine
centered identities (10), and the two eligible origin identities (16)
passed. The code also checks all twelve row means required by these
instances, all fifteen auxiliary Fourier identities (17), and the
exact rational fourth moments used to check (18)--(19) at these
primes. No floating-point character values enter the checks.

The full \(S_2\) fourth moments obtained in these three finite cases
are \(18,160,518\), respectively. These values are validation data,
not a proof of a general fourth-moment formula.

The saved record is
[centered_fourier_exact.json](centered_fourier_exact.json).
From the repository root, reproduce it with:

    python3 research/type_iii/contractions/centered_fourier_exact.py

The derivations above prove their stated identities and error bounds
for all primes. The finite checker is independent bounded validation;
it does not establish the remaining centered Fourier estimate.
