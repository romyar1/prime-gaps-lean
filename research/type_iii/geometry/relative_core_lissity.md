# The corrected correlation is lisse on the whole parameter torus

This is a mathematical proof using established étale-cohomology theorems,
not a Lean proof. It supplies a stronger construction of the actual
rank-six family used in the Type III proposition. No original manuscript
or formal source was changed.

## Statement and conventions

Fix a prime \(p>3\), an auxiliary prime \(\ell\ne p\), and a nontrivial
additive character \(\psi:\mathbf F_p\to\overline{\mathbf Q}_\ell^\times\).
Let \(\mathcal K_\psi\) be the normalized rank-three Kloosterman sheaf:
the usual weight-two sheaf with its integer Tate twist by \(1\).
Its trace over \(\mathbf F_q\), \(q=p^d\), is
\[
 K_{3,q}(a)=q^{-1}\sum_{u,v\in\mathbf F_q^\times}
       \psi(\operatorname {Tr}_{q/p}(u+v+a/(uv))).
\]
Put \(S=\mathbf G_{m,\lambda}\times\mathbf G_{m,\xi}\),
\(V=\mathbf G_{m,x}\times S\), and \(f:V\to S\). Define
\[
 \mathcal F_\psi=
 \mathcal K_\psi(x)\otimes\mathcal K_\psi(\lambda x)^\vee
              \otimes\mathcal L_\psi(\xi x).
\]
The following sheaf is lisse of rank six on **all** of \(S\):
\[
 \mathcal H_\psi^{\rm par}
  =\operatorname {im}\bigl(R^1f_!\mathcal F_\psi
                   \longrightarrow R^1f_*\mathcal F_\psi\bigr).
 \tag{1}
\]
Its formation commutes with base change on \(S\), and at every geometric
point \(s=(\lambda,\xi)\) its fiber is canonically
\[
 H^1\bigl(\mathbf P^1,\bar j_*\mathcal F_{\psi,s}\bigr),
 \qquad \bar j:\mathbf G_m\hookrightarrow\mathbf P^1.
 \tag{2}
\]
Here \(\bar j_*\) is the ordinary direct image. The sheaf in (1) is
pointwise pure of weight one. Tensor it with the constant rank-one Weil
sheaf \(\varepsilon\) whose \(\mathbf F_p\)-Frobenius is \(-1\); denote
the result by \(\mathcal H_\psi\). At \(\mathbf F_p\)-points,
\[
 t_{\mathcal H_\psi}(\lambda,\xi)
 = C_p(\xi^{-1},\lambda\xi^{-1},1)+1+p^{-1}+p^{-2}.
 \tag{3}
\]
Thus this is the actual corrected correlation, not a surrogate function.

## Constant conductor gives the two lisse rank-nine systems

Compactify \(f\) to the smooth proper relative curve
\(\bar f:\mathbf P^1\times S\to S\). Its missing divisor is the disjoint
union of the two sections \(x=0,\infty\). The input has rank nine.

At zero it is tame: both Kloosterman factors have one unipotent block
of length three, and the additive factor is unramified. At infinity
the tensor of the two Kloosterman factors has slopes at most \(1/3\).
Because \(\xi\ne0\), the additive factor has slope one; tensoring with
it makes every one of the nine slopes equal to one. Consequently
\[
 \operatorname {Sw}_0(\mathcal F_{\psi,s})=0,\qquad
 \operatorname {Sw}_\infty(\mathcal F_{\psi,s})=9
 \tag{4}
\]
for every geometric \(s\), including \(\lambda=1\).

The precise input is Deligne's conductor theorem as proved in
[Laumon, *Semi-continuité du conducteur de Swan*, Theorem 2.1.1,
Corollary 2.1.2 and Remark 2.1.3, pp. 185–187](https://www.numdam.org/article/AST_1981__82-83__173_0.pdf).
It treats a smooth separated relative curve over an excellent noetherian
base, a finite flat boundary, and a lisse constant-rank sheaf. If the
sum of the boundary Swan conductors plus ranks is locally constant,
extension by zero is universally locally acyclic over the base.
For a proper relative curve the resulting higher direct images are
lisse. The displayed theorem is stated with finite coefficients.

Its hypotheses here hold literally: \(S\) is smooth of finite type,
the boundary is two disjoint sections, and the conductor function is
\((0+9)+(9+9)=27\). Apply the same argument to \(\mathcal F_\psi^\vee\);
duality preserves the slopes and Swan conductors.

For completeness the finite-coefficient statement passes to this
\(\ell\)-adic application as follows. Choose a stable lattice over the
integers of a finite coefficient extension. Wild inertia has finite
\(p\)-group image, and reduction modulo a prime above \(\ell\) preserves
its invariant dimensions because \(p\ne\ell\). Hence the Swan
conductors of the reduction are the same as those of the lattice,
with the harmless residue-field multiplicity when viewed over
\(\mathbf F_\ell\). The conductor theorem applies to this reduction.
Local acyclicity is stable under extensions, so it applies successively
to all lattice quotients. Passage to the associated \(\ell\)-adic
complex gives the claimed lissity. No constancy of tame invariant
dimensions modulo \(\ell\) is needed in this step.

Compact-support base change identifies the fibers of \(R^if_!\) with
compact-support cohomology. The all-slope-one inertia at infinity
excludes invariant vectors in both \(\mathcal F_{\psi,s}\) and its
dual. Thus \(H_c^0=H_c^2=0\). Since
\(\chi_c(\mathbf G_m,\mathcal F_{\psi,s})=-9\), the sheaves
\[
 V_!=R^1f_!\mathcal F_\psi,\qquad
 V_!^\vee{}'=R^1f_!(\mathcal F_\psi^\vee)
\]
are lisse of rank nine, and the other direct images vanish.

Relative Poincaré duality identifies
\[
 R^1f_*\mathcal F_\psi
 \simeq \bigl(R^1f_!(\mathcal F_\psi^\vee)\bigr)^\vee(-1).
 \tag{5}
\]
It is therefore lisse of rank nine as well. The duality identification
is compatible with base change; together with compact-support base
change this proves base change for \(R^1f_*\) here. Thus (1) is the
image of a morphism of lisse sheaves. Images in this category are lisse,
and pullback is exact. This avoids the invalid inference that constant
fiber ranks alone imply lissity.

There is also a precise published reference for the base-change step:
[Quantitative sheaf theory, proof of Theorem 6.27, Step 1](https://arxiv.org/pdf/2101.00635v4)
states this implication on the whole base when \(f\) is smooth, the
input is lisse, and every \(R^if_!\) of its naive dual is lisse.
It cites Deligne, SGA \(4\frac12\), *Théorèmes de finitude*, 2.1.
All these hypotheses were checked above.

## Rank six, the boundary correction, and purity

For a smooth curve, the image of \(H_c^1(V_s,\mathcal F_s)\to
H^1(V_s,\mathcal F_s)\) is the parabolic cohomology (2). One can see
this from the ordinary-sheaf exact sequence comparing \(\bar j_!\)
and \(\bar j_*\), followed by the beginning of the Leray sequence
for \(\bar j\).

The invariant stalk at infinity is zero. At zero the invariant space
is the centralizer of one regular nilpotent \(3\)-by-\(3\) matrix:
\[
 \mathcal F_{\psi,s}^{I_0}=\langle I,N,N^2\rangle.
\]
It has dimension three for every \(\lambda\ne0\). There are no
global invariant vectors, so the boundary exact sequence gives
\[
 0\longrightarrow \mathcal F_{\psi,s}^{I_0}
 \longrightarrow H_c^1(\mathbf G_m,\mathcal F_{\psi,s})
 \longrightarrow H^1(\mathbf P^1,\bar j_*\mathcal F_{\psi,s})
 \longrightarrow0.
 \tag{6}
\]
The last space has dimension \(9-3=6\).

At a degree-\(d\) closed point with residue field \(\mathbf F_q\),
geometric Frobenius conjugates \(N\) to \(q^{-1}N\). Scaling by
\(\lambda\) changes the compatible Frobenius lift only by a unipotent
factor. The zero-stalk trace is therefore
\(\kappa_q=1+q^{-1}+q^{-2}\).
With \(A=\xi^{-1}\), \(B=\lambda\xi^{-1}\), the substitution \(x=Ah\)
in the original finite sum and the trace formula give
\[
 \operatorname {Tr}(\operatorname {Fr}_q\mid
                  \mathcal H_{\psi,s}^{\rm par})
 =-\bigl(C_q(A,B,1)+\kappa_q\bigr).
 \tag{7}
\]
After the sign twist the trace is
\((-1)^{d+1}(C_q(A,B,1)+\kappa_q)\). In particular (3) holds
when \(d=1\). The sign twist should not be said to produce the
unsigned corrected trace over every extension field.

The input on the curve is pure of weight zero. The complete-curve
purity theorem makes (2) pure of weight one:
[Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles
et conjecture de Weil*, Theorem 4.1.3](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf).
The sign twist has weight zero. This proves the claimed purity and
the uniform entry bound \( |C_p(A,B,1)|\le6\sqrt p+\kappa_p \)
at every pair of units.

## Consequences for the physical family

On \(T=\mathbf G_{m,r_1}\times\mathbf G_{m,r_2}\), the entry map to \(S\) is
\[
 \phi_{mn}(r_1,r_2)=
 \left(\frac{m r_1^3}{n r_2^3},
       \frac{m r_1^2}{\alpha r_2}\right).
 \tag{8}
\]
Every entry \(\phi_{mn}^*\mathcal H_\psi\) is lisse on all of \(T\).
For a conjugated entry use its dual twisted by \(-1\); this remains
pure of weight one. Every nonempty subproduct is consequently lisse
and pure on the same fixed torus, for every unit parameter tuple.

Thus one can use the canonical open immersion \(T\hookrightarrow
\mathbf A^2\) for intermediate extension. Generic base change, selection
of a principal open, dominance of the parameter map, and restoration of
discarded torus points are unnecessary for this construction. The
comparison between the intermediate-extension trace and extension by
zero on the two coordinate axes is still required.

Uniform complexity follows from the fixed-degree maps and the usual
complexity bounds for the six operations and cohomology; the image in
(1) may be bounded through kernels/cokernels or perverse subquotients
after shifting lisse sheaves by \(\dim S\). This step uses
[Quantitative sheaf theory, Theorems 6.8 and 6.15, Corollary 6.16,
and Proposition 6.24](https://arxiv.org/pdf/2101.00635v4).
It is a complexity argument in addition to lissity, not a consequence
of the fixed rank alone.

## The exceptional value \(\lambda=1\)

Whole-torus lissity is compatible with a change of ramification at the
excluded Fourier boundary \(\xi=0\). The six wild local phases quoted
in the manuscript are valid for generic \(\lambda\), not for
\(\lambda=1\). At \(\lambda=1\) one of the three coefficients
\(d_j=1-q_j\), \(q_j^3=\lambda\), is zero. Only the other two
rank-three blocks give the four slope-\(1/2\) dimensions; the remaining
two dimensions of the rank-six transform are tame at \(\xi=0\).

This does not obstruct the Type III generic-ray argument. On
\((r_1,r_2)=(t,zt)\) with \(z\) transcendental,
\(\lambda=m/(nz^3)\ne1\) for every nonzero \(m,n\), including repeated
row or column indices. A constant-ray specialization must omit the
cubic branch directions, as the revised manuscript already does.

The original generic six-character statement is supplied by
[Fu, Theorem 0.1(iii) and Proposition 0.8](https://arxiv.org/pdf/math/0702436v5).
The image construction above proves no further cancellation estimate
by itself.
