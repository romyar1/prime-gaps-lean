# The rank-six core, coefficient covariance, and finite ordinary support

Date: 4 September 2026.

This audit checks the actual constructions in [relative_core_lissity.md](relative_core_lissity.md) and [cyclotomic_support_rigidity.md](cyclotomic_support_rigidity.md). No mathematical error was found in their whole-torus rank-six construction, coefficient-change isomorphism, or deduction of finite ordinary degree \(-1\) support once all Fourier constituents have full support. The argument can be made more precise in three useful ways:

1. Construct the coefficient-change isomorphism over the finite coefficient field \(\mathbf Q_2(\zeta_p)\).
2. Use the strict boundary condition directly; geometric semisimplicity is unnecessary for the finite-support step.
3. Bound the cardinality of a finite ordinary support directly by the complexity of that cohomology sheaf.

The exclusion of constant and origin-line constituents through the exhaustive local character calculation is a separate input and is not proved in this audit.

## 1. Construction on the entire parameter torus

Fix \(p>3\), put \(E=\mathbf Q_2(\zeta_p)\), and choose \(\psi(t)=\zeta_p^t\). All Frobenius operators below are geometric. Let
\[
 \pi:\mathbf G_m^3\longrightarrow\mathbf G_m,\qquad
 \pi(u,v,w)=uvw,
 \qquad
 \mathcal K_\psi=R^2\pi_!\mathcal L_\psi(u+v+w)(1).
\]
This is the normalized rank-three Kloosterman sheaf. The cohomological construction and concentration in degree two are the \(n=3\) specialization of [Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, §§5.4–5.5; Theorem 4.1.1](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf). Its trace is the positive sum \(q^{-1}\sum_{uvw=a}\psi(\operatorname{Tr}_{q/p}(u+v+w))\): the cohomological sign is \((-1)^2=1\).

Set
\[
 S=\mathbf G_{m,\lambda}\times\mathbf G_{m,\xi},\quad
 V=\mathbf G_{m,x}\times S,\quad f:V\to S,
\]
\[
 \mathcal F=\mathcal K_\psi(x)\otimes
       \mathcal K_\psi(\lambda x)^\vee\otimes
       \mathcal L_\psi(\xi x).
\]
At every geometric point of \(S\), the rank is nine and the input is pure of weight zero. At \(x=0\) it is tame. At \(x=\infty\), the two Kloosterman factors have slopes \(1/3\); their tensor has slopes at most \(1/3\). Tensoring with the nontrivial slope-one character \(\mathcal L_\psi(\xi x)\) makes all nine slopes one. Thus
\[
 \operatorname{Sw}_0(\mathcal F_s)=0,\qquad
 \operatorname{Sw}_\infty(\mathcal F_s)=9.
\]
This includes \(\lambda=1\). The possible cancellation inside the Kloosterman tensor does not cancel its subsequent slope-one additive twist.

Compactify to \(\mathbf P^1\times S\). The two missing sections are finite flat over the smooth excellent noetherian base \(S\), and the boundary conductor function is the constant \(27\). These are precisely the hypotheses of [Laumon, Semi-continuité du conducteur de Swan, Theorem 2.1.1(ii) and Corollary 2.1.2, pp. 185–187](https://www.numdam.org/article/AST_1981__82-83__173_0.pdf). For the finite-coefficient theorem, reduce a stable lattice: wild inertia has finite \(p\)-group image, and averaging over that image preserves invariant dimensions modulo \(2\). The Swan conductors therefore remain constant. Extension through successive lattice quotients and passage to \(E\)-coefficients give the required lissity.

There are no global invariants or coinvariants because of the all-wild inertia at infinity. The Euler characteristic on \(\mathbf G_m\) is \(-9\). Consequently \(Rf_!\mathcal F\) and \(Rf_!\mathcal F^\vee\) are concentrated in degree one, with rank-nine lisse cohomology. Relative duality gives, with the indicated twist,
\[
 R^1f_*\mathcal F
   \simeq\bigl(R^1f_!\mathcal F^\vee\bigr)^\vee(-1).
\]
This also proves arbitrary base change for \(R^1f_*\) here. The applicable published statement is [Quantitative sheaf theory, proof of Theorem 6.27, Step 1, p. 42](https://arxiv.org/pdf/2101.00635v4): smooth \(f\), lisse input, and lissity of all compact direct images of its naive dual imply base change on the whole base.

Define the actual family by the image
\[
 \mathcal H^{\rm par}
 =\operatorname{im}(R^1f_!\mathcal F\longrightarrow R^1f_*\mathcal F).
\]
An image of a morphism of lisse \(E\)-sheaves is lisse; pullback is exact on these sheaves. Its formation therefore commutes with arbitrary base change. This argument does not assume base change for a relative ordinary \(j_*\).

On a geometric fiber, the usual boundary exact sequence and the Leray sequence identify the image with
\[
 H^1(\mathbf P^1,\bar j_*\mathcal F_s).
\]
At zero, the two regular unipotent rank-three inertia representations give
\[
 \mathcal F_s^{I_0}
   =\operatorname{Hom}_{I_0}(\mathcal K_\psi(\lambda x),
                            \mathcal K_\psi(x))
   \simeq\langle I,N,N^2\rangle.
\]
At infinity the invariant space is zero. The exact sequence
\[
 0\to\mathcal F_s^{I_0}\to H_c^1(\mathbf G_m,\mathcal F_s)
   \to H^1(\mathbf P^1,\bar j_*\mathcal F_s)\to0
\]
therefore gives rank \(9-3=6\), including every unit specialization. The regular unipotent assertion and zero-invariant Frobenius normalization are [Katz, Theorem 7.4.3, pp. 108–109](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf).

The last cohomology group is pure of weight one by [Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de Weil, Theorem 4.1.3, p. 204](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf). Its hypotheses are exactly a smooth projective curve, a dense open, and a lisse pure input on that open; no generic-\(\lambda\) hypothesis occurs.

## 2. Arithmetic trace, sign, and conjugate factor

At \(s=(\lambda,\xi)\) rational over \(q=p^d\), write \(A=\xi^{-1}\), \(B=\lambda\xi^{-1}\). Scaling \(x=Ah\) identifies the trace sum of \(\mathcal F_s\) with \(C_q(A,B,1)\).

The normalized Kloosterman Frobenius acts on its monodromy filtration with eigenvalues \(q^{-1},1,q\). On the three-dimensional intertwiner space above, the diagonal eigenvalues are \(1,q^{-1},q^{-2}\). Changing the tangent coordinate by the unit \(\lambda\) changes a Frobenius lift by a unipotent inertia factor and does not change this trace. Thus its boundary contribution is
\[
 \kappa_q=1+q^{-1}+q^{-2}.
\]
The trace formula and the exact sequence give
\[
 \operatorname{Tr}(\operatorname{Fr}_q\mid\mathcal H_s^{\rm par})
     =-C_q(A,B,1)-\kappa_q.
\]
Let \(\varepsilon\) be the constant rank-one Weil sheaf whose \(p\)-Frobenius is \(-1\), and put \(\mathcal H=\mathcal H^{\rm par}\otimes\varepsilon\). Then
\[
 t_{\mathcal H}(s)=(-1)^{d+1}
                      \bigl(C_q(A,B,1)+\kappa_q\bigr).
\]
In particular, at prime-field points this is exactly the corrected correlation. The unsigned formula must not be extended to even \(d\).

For a conjugated corrected factor the correct sheaf is \(\mathcal H^\vee(-1)\). Purity of weight one gives \(q/\alpha=\overline\alpha\) for its Frobenius eigenvalues after the chosen complex embedding, so this dual-and-twist operation has the required conjugate trace. It remains pure of weight one. The twist \((-1)\) cannot be omitted.

## 3. The actual coefficient-change isomorphism

The extension \(E/\mathbf Q_2\) is unramified. Its Frobenius automorphism \(\tau\) sends \(\zeta_p\) to \(\zeta_p^2\). This finite-field-of-coefficients formulation follows from [Milne, Algebraic Number Theory, Proposition 7.50, Corollary 7.51, and Example 7.54](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

Transport of coefficients by \(\tau\) is an exact equivalence: apply \(\tau\) to representation matrices. It commutes with the derived sheaf operations and fixes \(E(1)\), \(E(-1)\), and \(\varepsilon\). All constructions above take place over \(E\), so an arbitrary automorphism of \(\mathbf C\) is unnecessary.

Multiplication of all three product-map coordinates by two gives
\[
 {}^\tau\mathcal K_\psi\simeq[8]^*\mathcal K_\psi.
\]
There is also a direct source: [Katz, Lemma 4.1.9, p. 53](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf). The auxiliary extension degree in that lemma is one here because all multiplicative characters are trivial.

Define the two isomorphisms
\[
 b(\lambda,\xi)=(\lambda,\xi/4),\qquad
 a(x,\lambda,\xi)=(8x,\lambda,\xi/4).
\]
Then \(f\circ a=b\circ f\), and
\[
 {}^\tau\mathcal F\simeq a^*\mathcal F,
 \qquad
 (\xi/4)(8x)=2\xi x.
\]
This is a Cartesian square of isomorphisms. The natural map from compact to ordinary direct image is compatible with it, so taking \(R^1\) and its lisse image gives
\[
 {}^\tau\mathcal H\simeq b^*\mathcal H.
\]
No generic base-change theorem or deletion of parameter fibers is used in this step.

For nonzero \(\alpha,m,n\), the physical map
\[
 \phi_{mn}(r_1,r_2)=
 \left(\frac{mr_1^3}{nr_2^3},\frac{mr_1^2}{\alpha r_2}\right)
\]
satisfies \(\phi_{mn}\circ s_{1/4}=b\circ\phi_{mn}\). Hence every physical corrected factor, including its conjugate representative, satisfies the same scalar pullback isomorphism. For any nonempty tensor subproduct \(\mathcal G\), put
\[
 P=j_{!*}(\mathcal G[2]),\qquad
 j:\mathbf G_m^2\hookrightarrow\mathbf A^2,\qquad
 Q=\operatorname{FT}_\psi(P).
\]
The torus is invariant, so \({}^\tau P\simeq s_{1/4}^*P\). In the Fourier integral substitute \(r=4u\):
\[
 {}^\tau Q
 \simeq\operatorname{FT}_{\psi_2}(s_{1/4}^*P)
 \simeq s_8^*\operatorname{FT}_\psi(P).
\]
The phase is \(2(4u\cdot\eta)=u\cdot8\eta\). Both Fourier transforms use shift \([2]\); an isomorphism of integration spaces introduces no degree factor or Tate twist. This is the scalar-isomorphism case of [Laumon, Theorem 1.2.2.4; base change is Proposition 1.2.2.9](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf).

Thus the claimed isomorphism is a valid consequence of the actual construction for all unit parameter tuples, repeated or distinct.

## 4. Why the ordinary degree \(-1\) support becomes finite

This step is valid even without purity. Let \(Q\) be perverse on \(\mathbf A^2_{\overline{\mathbf F}_p}\) with every simple constituent of full support. Choose a dense open \(U\) on which \(Q=L[2]\), with \(L\) lisse. No nonzero subobject or quotient can be supported on the complement. Therefore
\[
 Q=j_{!*}(L[2]).
\]
By [BBD, Corollaries 1.4.24–1.4.25, p. 55](https://publications.ias.edu/sites/default/files/Faisceaux%20pervers.pdf), for the boundary inclusion \(i\),
\[
 i^*Q\in{}^pD^{\le-1}.
\]
The middle-perversity support condition gives
\[
 \dim\operatorname{supp}\mathcal H^r(i^*Q)\le-r-1.
\]
Since \(Q=L[2]\) on \(U\), this proves
\[
 \mathcal H^0(Q)=0,\qquad
 \dim\operatorname{supp}\mathcal H^{-1}(Q)\le0.
\]
Constructibility makes the latter support a finite geometric set. The standard amplitude on a surface leaves only degrees \(-2,-1\).

The geometric hypothesis must concern all simple constituents. Full support of the whole complex, or lissity on a dense open, would not exclude an additional curve-supported summand.

For the actual \(P\), a \(w\)-factor product has weight \(w+2\); the affine open immersion preserves purity of intermediate extension by BBD Corollary 5.3.2. Fourier transform is perverse by Laumon Theorem 1.3.2.3, and \(Q\) has weight \(w+4\) by [Katz–Laumon, Theorem 2.2.1, p. 155](https://www.numdam.org/article/PMIHES_1985__62__145_0.pdf). The later published correction concerns §4's shifts and signs, not this theorem.

## 5. Uniformity and the precise remaining dependency

Fixed-degree maps and rational phases bound the complexity of the construction uniformly in \(p\) and every unit specialization. The rank-six image is a perverse subquotient of \(R^1f_!\mathcal F[2]\). The applicable bounds are [Quantitative sheaf theory, Theorems 6.8 and 6.15, Corollaries 6.16 and 7.7, Proposition 6.19, and Proposition 7.18](https://arxiv.org/pdf/2101.00635v4). These are uniform complexity bounds, not a conclusion from rank alone.

There is a direct cardinality argument once \(M=\mathcal H^{-1}(Q)\) has finite support \(Z\). Extension by zero to \(\mathbf P^2\) has only degree-zero cohomology, equal to \(\bigoplus_{z\in Z}M_z\); generic lines and points avoid \(Z\). Definition 3.2 therefore gives
\[
 |Z|\le\sum_{z\in Z}\dim M_z=c(M)
       \le N(2,c(Q))
\]
by QST Proposition 6.24. No new generic-open choice is necessary.

Coefficient transport preserves ordinary stalk dimensions. The established isomorphism \({}^\tau Q\simeq s_8^*Q\) therefore makes \(Z\) eight-invariant. If \(c(Q)\le C_0\) uniformly, choose \(D\) to dominate \(N(2,n)\) for the finitely many integers \(0\le n\le C_0\); no monotonicity of \(N\) is required. For \(p>8^D\), the already proved finite-orbit lemma forces \(Z\subset\{0\}\).

With uniformly bounded stalk dimensions, the weight bounds on degrees \(-2\) and \(-1\) give
\[
 |t_Q(h,k)|\ll
 p^{(w+2)/2}
 +p^{(w+3)/2}\mathbf1_{(h,k)=0}.
\]
These exponents and the absence of degree zero are consistent with the Fourier convention.

The remaining decisive mathematical premise for this deduction is the exclusion of every curve and punctual constituent of the actual Fourier transforms. The proposed angular and radial character calculation must establish that exclusion for every distinct-index tuple. Whole-torus lissity and the coefficient isomorphism establish no such exclusion by themselves. In particular, the generic six-wild-character description must still be connected to the full ordinary-\(j_*\) correlation transform; \(\lambda=1\) has a tame remainder. The coordinate-axis comparison with the raw zero extension and the four-factor correction expansion also remain necessary when returning from \(t_Q\) to the requested finite sum.
