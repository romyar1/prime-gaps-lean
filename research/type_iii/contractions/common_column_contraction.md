# Exact common-column contraction for the actual Type III correlation

Status: a finite-sum derivation, exact bounded validation, and an independent
matrix norm consequence. The exceptional Fourier estimate for an individual
four-cycle is **not** obtained here. This note does not alter a manuscript or
introduce an analytic hypothesis into the Lean development.

## 1. Normalization and the existing exact input

Let \(p\) be a prime, let \(G=\mathbf F_p^\times\), and write
\(\psi(x)=\exp(2\pi i x/p)\). All sums below are unnormalized sums. Set

\[
 f(t)=\frac1p\sum_{u,v\in G}\psi\left(u+v+\frac{t}{uv}\right),
 \qquad
 S_2(t)=\sum_{u\in G}\psi\left(u+\frac{t}{u}\right).
\]

Thus \(f(t)\) is `PrimeGap182.TypeIII.kl3 p t`, and \(S_2(t)\) is
`PrimeGap186.unnormalizedKloosterman2 p t`. In particular, there is no
factor \(p^{-1/2}\) in \(S_2\). Define

\[
 C_c(A,B)=\sum_{h\in G} f(Ah)\overline{f(Bh)}\psi(ch),
 \qquad \kappa=1+p^{-1}+p^{-2},
\]

and write \(C(A,B)=C_1(A,B)\). This is precisely the definition of
`correlation p A B c` in
[TypeIIILocal.lean](../../../formal/TypeIIILocal.lean#L35).

The already proved exact orthogonality identity is

\[
 \sum_{x\in G} f(ax)\overline{f(bx)}
       =p\mathbf1_{a=b}-\kappa \qquad (a,b\in G).
 \tag{1}
\]

This is `correlation_zero` in
[TypeIIIBaselineBridge.lean](../../../formal/TypeIIIBaselineBridge.lean#L39),
which uses `PrimeGap186.normalizedKloosterman3_unit_correlation_zero` in
[the pinned public development](../../../vendor/primegaps186/PrimeGaps186.lean#L64452).
It is an exact finite Fourier identity, not the public Deligne bound.

We also need the unit Fourier transform

\[
 F_c(A)=\sum_{h\in G}f(Ah)\psi(ch).
 \tag{2}
\]

For \(A\ne0\), its exact value is

\[
 F_c(A)=
 \begin{cases}
 -p^{-1},&c=0,\\
 S_2(-A/c)-p^{-1},&c\ne0.
 \end{cases}
 \tag{3}
\]

To verify the sign and constant directly, include \(h=0\), interchange the
three sums, and apply additive orthogonality:

\[
 \begin{aligned}
 \sum_{h\in\mathbf F_p} f(Ah)\psi(ch)
 &=\frac1p\sum_{u,v\in G}\psi(u+v)
                  \sum_{h\in\mathbf F_p}\psi\bigl((A/(uv)+c)h\bigr)\\
 &=\begin{cases}
 0,&c=0,\\
 \displaystyle\sum_{u\in G}\psi\bigl(u-A/(cu)\bigr),&c\ne0.
 \end{cases}
 \end{aligned}
\]

Here \(A\ne0\) rules out \(A/(uv)=0\), and for \(c\ne0\) the equation is

\[
 uv=-A/c,\qquad v=-A/(cu).
\]

Finally \(f(0)=p^{-1}(\sum_{u\in G}\psi(u))^2=p^{-1}\), so deleting
the \(h=0\) term proves (3). The existing public helper is
`normalizedKloosterman3_unit_fourier`, with \(h=c/A\) after scaling the
unit variable; see
[the exact declaration](../../../vendor/primegaps186/PrimeGaps186.lean#L64056).
At \(A=0\), (2) is still defined, but (3) must instead be replaced by

\[
 F_c(0)=p^{-1}\bigl(p\mathbf1_{c=0}-1\bigr).
\]

Conjugation creates no hidden phase in the following identities. The
substitution \(u\mapsto-u\) gives \(\overline{S_2(t)}=S_2(t)\), and the
substitution \((u,v)\mapsto(-u,-v)\) gives
\(\overline{f(t)}=f(-t)\). Consequently, conjugating \(C_c(A,B)\) and
then replacing \(h\mapsto-h\) gives

\[
 \overline{C_c(A,B)}=C_c(A,B).
 \tag{4}
\]

These statements hold also in characteristic two. We nevertheless retain
the conjugates in the principal contraction and Gram identities so that
their orientation remains explicit.

## 2. The general contraction

For arbitrary \(A,A',c,d\in\mathbf F_p\) and \(\beta\in G\),

\[
 \boxed{
 \sum_{B\in G}C_c(A,B)\overline{C_d(A',\beta B)}
 =p C_{c\beta-d}(A\beta,A')
       -\kappa F_c(A)\overline{F_d(A')}.
 }
 \tag{5}
\]

Equivalently, after replacing the unit variable \(h\) by \(h/\beta\),

\[
 \boxed{
 \sum_{B\in G}C_c(A,B)\overline{C_d(A',\beta B)}
 =p C_{c-d/\beta}(A,A'/\beta)
       -\kappa F_c(A)\overline{F_d(A')}.
 }
 \tag{6}
\]

Only \(\beta\ne0\) is needed in these two formulas. Nonzero \(A,A'\)
are needed for (3), for (9) below, and for the quoted nonzero-argument
estimates.

**Proof.** Expanding both correlations and commuting finite sums gives

\[
 \begin{aligned}
 &\sum_{B\in G}C_c(A,B)\overline{C_d(A',\beta B)}\\
 &\quad=\sum_{h,h'\in G}
 f(Ah)\overline{f(A'h')}\psi(ch-dh')
 \sum_{B\in G}\overline{f(Bh)}f(\beta Bh').
 \end{aligned}
 \tag{7}
\]

The arguments \(h\) and \(\beta h'\) are nonzero. Formula (1), with its
two factors commuted, therefore evaluates the inner sum as

\[
 \sum_{B\in G}\overline{f(Bh)}f(\beta Bh')
       =p\mathbf1_{h=\beta h'}-\kappa.
 \tag{8}
\]

The indicator collapses \(h=\beta h'\), producing

\[
 p\sum_{h'\in G}f(A\beta h')\overline{f(A'h')}
                          \psi((c\beta-d)h')
 =p C_{c\beta-d}(A\beta,A').
\]

The constant part separates as

\[
 -\kappa
 \left(\sum_{h\in G}f(Ah)\psi(ch)\right)
 \overline{\left(\sum_{h'\in G}f(A'h')\psi(dh')\right)}.
\]

This proves (5). In its correlation term, set \(h'=h/\beta\); the three
arguments become \(A,A'/\beta,c-d/\beta\), proving (6).

## 3. Exact Gram matrix and the norm bound

Take \(c=d=\beta=1\) and \(A,A'\in G\), and put

\[
 U_A=F_1(A)=S_2(-A)-p^{-1}.
\]

Equations (1) and (6) give

\[
 \boxed{
 \sum_{B\in G} C(A,B)\overline{C(A',B)}
 =p^2\mathbf1_{A=A'}-p\kappa-\kappa U_A\overline{U_{A'}}.
 }
 \tag{9}
\]

Regard \(C=(C(A,B))_{A,B\in G}\) as a complex matrix whose **rows are
indexed by \(A\)** and **columns by \(B\)**. Let \(J\) denote the matrix
with every entry equal to one, and \(U\) the column with entries \(U_A\).
Then (9) reads

\[
 CC^*=p^2I-\kappa(pJ+UU^*).
 \tag{10}
\]

Thus, for every complex family \(z=(z_A)_{A\in G}\),

\[
 \begin{aligned}
 \sum_{B\in G}\left|\sum_{A\in G}z_A C(A,B)\right|^2
 &=p^2\sum_{A\in G}|z_A|^2
  -p\kappa\left|\sum_{A\in G}z_A\right|^2
  -\kappa\left|\sum_{A\in G}z_A U_A\right|^2\\
 &\le p^2\sum_{A\in G}|z_A|^2.
 \end{aligned}
 \tag{11}
\]

Because \(\kappa>0\), the correction in (10) is positive semidefinite.
Consequently the Euclidean operator norm satisfies

\[
 \boxed{\|C\|_{2\to2}\le p.}
 \tag{12}
\]

Neither a bound for \(S_2\) nor any other character-sum estimate enters
(9)--(12). This is a uniform **matrix** estimate, not a bound for the
two-dimensional Fourier transform of a four-cycle.

There is also a shorter factorization proof of (12). For

\[
 H_{A,h}=f(Ah),\qquad D_{h,h}=\psi(h),
\]

we have \(C=HDH^*\), \(HH^*=pI-\kappa J\), and \(D\) is unitary.
Hence \(\|H\|^2\le p\), and \(\|C\|\le\|H\|^2\le p\).
The explicit rank-two correction in (10) contains additional information
beyond this factorization.

### Application to the actual physical kernel matrix

Fix \(\alpha\ne0\) and physical coordinates \(r_1,r_2\ne0\). Set

\[
 A_0=\frac{\alpha r_2}{r_1^2},\qquad
 B_0=\frac{\alpha r_1}{r_2^2}.
\]

The matrix with rows \(m\in G\), columns \(n\in G\), and entries equal
to the actual `kernel` is

\[
 K_{m,n}=C(A_0/m,B_0/n).
 \tag{13}
\]

The maps \(m\mapsto A_0/m\), \(n\mapsto B_0/n\) are bijections of
\(G\), so (13) is obtained from \(C\) by independent row and column
permutations. Its norm is therefore at most \(p\). If either physical
coordinate is zero, the `kernel` definition makes the entire matrix zero.
Restricting to subsets of the row and column unit classes also preserves
the bound.

For a squarefree modulus \(q=\prod_i p_i\), the complete unit-indexed
`squarefreeKernel` matrix is, under CRT, the tensor product of the local
matrices. Its norm is at most \(\prod_i p_i=q\). This uses pairwise
distinct primes and nonzero local values of \(\alpha_i\).

The actual
[integer kernel](../../../formal/TypeIIIIntegerKernel.lean#L27)
sets nonunit integer rows and columns to zero. On intervals containing
\(N\) row indices and \(M\) column indices, each residue class modulo
\(q\) occurs at most \(\lceil N/q\rceil\) or \(\lceil M/q\rceil\)
times. The two residue duplication maps have norms at most the square
roots of these multiplicities. Consequently, for every fixed physical
residue pair,

\[
 \boxed{
 \|\operatorname{integerKernelMatrix}\|_{2\to2}
 \le q\sqrt{\lceil N/q\rceil\lceil M/q\rceil}.
 }
 \tag{14}
\]

For example, when \(N,M\le q\), this gives \(\|K\|\le q\).
Using only (14), an outer rectangle with \(H\) by \(L\) integer
positions has fourth-moment bound

\[
 \sum_{x,y}\|K_{x,y}\|^4
 \le HL\,q^4\lceil N/q\rceil^2\lceil M/q\rceil^2.
 \tag{15}
\]

This does not reproduce the parameter-dependent cancellation terms in
`integerKernelMatrix_fourth_moment_bound`. Its usefulness in a particular
analytic range must be checked by comparing (15) with the required
estimate. The CRT and interval statements here are ordinary linear
algebra deductions; they have not been added to shared Lean files by
this task.

## 4. A shifted contraction using existing analytic inputs

Suppose \(A,A',\beta\in G\) and \(\beta\ne1\). At \(c=d=1\),
the first term in (6) has a nonzero additive frequency and can be
normalized:

\[
 C_{1-1/\beta}(A,A'/\beta)
 =C_1\left(\frac{\beta A}{\beta-1},\frac{A'}{\beta-1}\right).
 \tag{16}
\]

The existing pair-correlation estimate in
`correlation_norm_le_of_baseline_inputs` bounds (16) by \(9\sqrt p\).
Combining (6) with the existing classical bound
\( |S_2(t)|\le2\sqrt p\) for \(t\ne0\) gives

\[
 \left|\sum_{B\in G}C(A,B)\overline{C(A',\beta B)}\right|
 \le 9p^{3/2}+\kappa(2\sqrt p+p^{-1})^2.
 \tag{17}
\]

The scalar rank-two bound is the public theorem
`unnormalizedKloosterman2_norm_le_two_mul_sqrt` in
[PrimeGaps186.lean](../../../vendor/primegaps186/PrimeGaps186.lean#L65758).
Its proof invokes the public rational-sum Weil input. It is a separate
dependency from the two statements packaged into `BaselineLocalInputs`;
this note does not silently add it to that package. Formulas (5)--(15)
do not need it.

Thus a product of two correlations can, after a complete common-column
sum, be reduced to the already used two-rank-two correlation estimate
and a rank-one correction. A product of four correlations with a fixed
row ratio does not yet admit this contraction.

## 5. Two further exact checks on the orientation

The following consequences were included in the small-prime validation.
They distinguish a complete contraction from the unresolved individual
four-cycle sum.

### Two-factor moment and the cubic torus map

For \(a,b\in G\), define

\[
 T(a,b)=\sum_{A,B\in G}C(A,B)\overline{C(aA,bB)}.
\]

Then

\[
 \boxed{
 T(a,b)=p^3\mathbf1_{a=b=1}-p^2\mathbf1_{a=b}
       -p^2\kappa(\mathbf1_{a=1}+\mathbf1_{b=1})
       +2p\kappa+\kappa^2.
 }
 \tag{18}
\]

Indeed, the existing rank-two unit correlation identity gives

\[
 \sum_{A\in G}U_A\overline{U_{aA}}
       =p^2\mathbf1_{a=1}-p-\kappa.
 \tag{19}
\]

The correction terms in (19) use \(\sum_{A\in G}S_2(-A)=1\).
Sum (6), with \(A'=aA,\beta=b,c=d=1\), over \(A\). By interchanging
\(A,h\) and using (1), its first correlation term becomes

\[
 p\sum_{A\in G}C_{1-1/b}(A,aA/b)
 =p\bigl(p\mathbf1_{a=b}-\kappa\bigr)
       \bigl(p\mathbf1_{b=1}-1\bigr).
\]

Subtract \(\kappa\) times (19) and expand to obtain (18). In
particular,

\[
 \sum_{A,B\in G}|C(A,B)|^2
 =T(1,1)=p^3-3p^2+2/p+\kappa^2.
 \tag{20}
\]

If \(\gcd(3,p-1)=1\), the physical map

\[
 (r_1,r_2)\longmapsto(r_2/r_1^2,r_1/r_2^2)
\]

is a bijection of \(G^2\). This fact is already formalized by
`exactUnitTorusMap_bijective` and used by
`exact_torus_pullback_origin_of_coprime` in
[TypeIIITraceIdentity.lean](../../../formal/TypeIIITraceIdentity.lean).
Thus (18) also evaluates the actual zero-frequency coefficient of

\[
 K_{\alpha;m,n}(r_1,r_2)
       \overline{K_{\alpha;m',n'}(r_1,r_2)},
 \qquad a=m/m',\quad b=n/n',
\]

under these hypotheses. This is a **two-factor** coefficient.

When \(p\equiv1\pmod3\), the physical map has three points above its
image, not one point above every unit pair. In fact the image condition
in the \(A,B\) coordinates of the first kernel is that
\(m^2nA^2B\) be a cube. Equivalently, for a nontrivial cubic character
\(\chi\), the unpulled sum carries the weight

\[
 1+\chi(m^2nA^2B)+\overline{\chi(m^2nA^2B)}.
\]

Formula (18) evaluates only its unweighted part. No assertion equating
(18) with the actual physical coefficient is made in this case.

### Signed average of the unpulled four-cycle

Set

\[
 R(a,b)=\sum_{A,B\in G}
 C(A,B)\overline{C(aA,B)}C(aA,bB)\overline{C(A,bB)}.
\]

For fixed \(b\ne1\), summing over **all** \(a\in G\) permits the
reindexing \(A'=aA\) and gives

\[
 \sum_{a\in G}R(a,b)
 =\sum_{B\in G}\left|\sum_{A\in G}
                  C(A,B)\overline{C(A,bB)}\right|^2.
 \tag{21}
\]

The column version of (9), obtained by transposing and replacing
frequency (1) by (-1), involves

\[
 V_B=F_{-1}(B)=S_2(B)-p^{-1}.
\]

Since \(bB\ne B\), it evaluates the inner sum in (21) as
\(-\kappa(p+V_BV_{bB})\). The plus sign in \(S_2(B)\), as opposed to
the minus sign in \(U_A=S_2(-A)-p^{-1}\), is necessary. Hence

\[
 \boxed{
 \sum_{a\in G}R(a,b)
   =\kappa^2\sum_{B\in G}(p+V_BV_{bB})^2\qquad(b\ne1).
 }
 \tag{22}
\]

The \(V_B\) are real by (4)'s rank-two conjugation argument. Using the
existing scalar rank-two bound, (22) implies

\[
 0\le\sum_{a\in G}R(a,b)
 \le\kappa^2(p-1)\bigl[p+(2\sqrt p+p^{-1})^2\bigr]^2
 =O(p^3).
 \tag{23}
\]

This is a signed parameter sum. It includes the repeated-row term
\(a=1\). It bounds neither an individual \(R(a,b)\) nor
\(\sum_a|R(a,b)|\). Passing from (23) to either of those conclusions
would discard the possible cancellation between row ratios.

## 6. Exact finite validation

The adjacent
[checker](pair_contraction_exact.py)
constructs \(p f(t)\) directly from the two-unit definition, as an
integer coefficient vector for powers of a formal \(\zeta_p\). It then
constructs \(p^2 C_c(A,B)\) directly from that table and the original
unit-indexed correlation. Polynomial products are computed modulo
\(X^p-1\), and an equality holds exactly when the coefficients of the
difference are all equal, equivalently when it is a multiple of
\(\Phi_p(X)=1+X+\cdots+X^{p-1}\). No complex floating-point values or
approximate comparisons enter these tests.

The direct correlation is separately checked against zero-frequency
orthogonality and frequency normalization before the normalized lookup
table is used in contraction tests. The \(F_c(A)\) formula is checked
directly for every \(A\in G,c\in\mathbf F_p\) at every listed prime.
The tests also check reality of \(C(A,B)\), (18), its actual two-factor
torus version when the cubic map is bijective, and (22).

| Prime | Frequencies in the contraction | Complete \(A,A',\beta\in G\) contraction checks | Normalization and reality checks | All-ratio two-factor checks | Actual torus two-factor checks | Signed four-cycle averages |
|---:|:---|---:|---:|---:|---:|---:|
| 2 | all \(c,d\in\mathbf F_2\) | 4 | 5 | 1 | 1 | 0 |
| 3 | all \(c,d\in\mathbf F_3\) | 72 | 22 | 4 | 4 | 1 |
| 5 | all \(c,d\in\mathbf F_5\) | 1,600 | 116 | 16 | 16 | 3 |
| 7 | \(c=d=1\) | 216 | 150 | 36 | 0 | 5 |
| 11 | \(c=d=1\) | 1,000 | 410 | 100 | 100 | 9 |
| **Total** | | **2,892** | **703** | **157** | **121** | **18** |

Every listed check passed. The stronger arbitrary-\(A,A'\) version (5)
is proved by the derivation in Section 2; this finite test receipt only
claims the displayed nonzero-\(A,A'\) ranges.

The resulting Frobenius-square values from (20) are respectively

\[
 \frac1{16},\quad\frac{223}{81},\quad\frac{32461}{625},\quad
 \frac{474531}{2401},\quad\frac{14192839}{14641}.
\]

The machine-readable record is
[pair_contraction_exact.json](pair_contraction_exact.json).
Reproduce from the repository root with

```sh
python3 research/type_iii/contractions/pair_contraction_exact.py
```

The receipt records the checker source SHA256. Its status is
`EXACT_FINITE_CONTRACTION_IDENTITIES_ONLY`; the script is not a
certificate for a uniform Fourier estimate. The unrestricted
finite-sum proofs are those given above, independently of the tests.

## 7. Exact remaining estimate and formalization handoff

For fixed distinct nonzero \(m,m'\) and \(n,n'\), the missing target is
still a bound for each Fourier coefficient of

\[
 W(r_1,r_2)=K_{m,n}(r_1,r_2)\overline{K_{m',n}(r_1,r_2)}
            K_{m',n'}(r_1,r_2)\overline{K_{m,n'}(r_1,r_2)}:
\]

\[
 \widehat W(h,k)=\sum_{r_1,r_2\in\mathbf F_p}
           W(r_1,r_2)\psi(hr_1+kr_2).
\]

The required finite-exceptional statement has constants independent of
\(p,\alpha,m,m',n,n'\): \(O(p^3)\) away from a bounded number of
frequencies and \(O(p^{7/2})\) at those exceptional frequencies. In
particular, the distinct-index branch does not permit an uncontrolled
\(p^4\) origin term. The exact Gram identity does not prove this
statement, at the origin or away from it.

At a fixed row ratio \(a\), the sum contains two extra \(B\)-dependent
correlation factors. They prevent applying (6) to the other pair as an
unweighted sum. A bound for an unweighted contraction cannot be
multiplied by a supremum of those weights to obtain a weighted
contraction bound. Moreover, the physical Fourier character becomes a
nonlinear weight after the torus change of variables, with cubic
fibers when \(p\equiv1\pmod3\). These are the parts not resolved by the
present algebra.

The useful formalization sequence communicated to
`/root/typeiii_exact_route_new` is:

1. Define \(F_c(A)\) using the actual `kl3` and prove (5) from
   `correlation_zero` by exchanging the three unit sums.
2. Give the divided-parameter version (6) by a unit reindexing.
3. Evaluate \(F_1(A)\) for unit \(A\), or retain its finite-sum form
   initially, and specialize to (9).
4. Prove the exact quadratic form (11), then the Euclidean operator norm
   bound (12), with no analytic character-sum axiom.
5. Treat any later use of (14), (17), or (23) as a distinct consequence
   with its own stated hypotheses. Neither this note nor its finite
   checker establishes the missing four-cycle Fourier proposition.
