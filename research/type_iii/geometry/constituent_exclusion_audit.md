# Focused audit of Type III constituent exclusion

Date: 4 September 2026.

**Finding.** This pass found no counterexample to the manuscript's exclusion of every curve and punctual Fourier constituent when the row indices and column indices are distinct and the characteristic exceeds the uniform support-degree bound. There is one precise identification which deserves an explicit statement and citation: the local Fourier transform computed by Fu must be connected to the actual ordinary-middle-extension correlation. The identification holds for every \(\lambda\ne1\); the unrestricted version at \(\lambda=1\) is false. The argument below supplies the missing explanation. It does not constitute a Lean verification.

The audited source is `finite_exceptional_type_iii_revised.tex` (not included in this repository or its source archive), SHA256
\[
\texttt{70657eac63b2f444f39e194bd8e49879daa5e0f711bf08ddab6621a61f0d89f9}.
\]
The relevant results are Corollary 6.1, Lemmas 7.1 and 7.2, and their application in Section 8. Local locators below refer to this unchanged source. The whole-torus construction and weights are treated separately in [core_covariance_and_finite_support_audit.md](core_covariance_and_finite_support_audit.md).

## 1. The exact missing bridge, and why it holds

Put \(j:\mathbf G_m\hookrightarrow\mathbf A^1\),
\[
 F_\lambda=\mathcal K(x)\otimes\mathcal K(\lambda x)^\vee,
 \qquad K_\lambda=j_*F_\lambda[1],
 \qquad K'_\lambda=\operatorname{FT}_\psi(K_\lambda).
\]
Here \(j_*\) denotes the ordinary direct image. On a smooth curve, \(K_\lambda\) is the perverse intermediate extension. On \(\xi\ne0\), write \(K'_\lambda=H_\lambda[1]\); the actual rank-six cohomology family, before its constant sign twist, is \(H_\lambda\).

The required statement is
\[
 H_\lambda|_{I_{\xi=0}}
 \simeq
 \mathcal F_\psi^{(\infty,0)}
       (F_\lambda|_{I_{x=\infty}})
 \qquad(\lambda\ne0,1).
 \tag{1}
\]
It concerns the actual local representation, including tame factors; it is stronger than a match of ranks or a trace identity.

The finite-point vanishing-cycle sequence in [Laumon, Section 2.3.2, p. 160](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf) is
\[
 0\longrightarrow \mathcal H^{-1}(K'_{\lambda,0})
 \longrightarrow H_{\lambda,\eta_0}
 \longrightarrow R^{-1}\Phi_0(K'_\lambda)
 \longrightarrow \mathcal H^0(K'_{\lambda,0})
 \longrightarrow0.
 \tag{2}
\]
The end terms have trivial geometric inertia. Proposition 2.3.2.1(iii), together with Lemma 2.4.2.1(ii), identifies the vanishing-cycle term with the local transform on the right of (1).

For \(\lambda\ne1\), the three Mackey summands have \(d=1-q\ne0\), \(q^3=\lambda\). Each contributes a rank-two, entirely wild local transform. Thus the middle target in (2) has six wild dimensions. The already established rank \(H_{\lambda,\eta_0}=6\) forces (2) to be an isomorphism with both end terms zero. This proves (1), so the six computed characters exhaust the actual correlation representation.

The manuscript's rank-exhaustion paragraph is at lines 722–726. Its sheaf-facts paragraph, lines 489–515, cites the infinity stationary-phase proposition 2.3.3.1, but does not explicitly give the finite-origin proposition 2.3.2.1 or sequence (2). This is an omitted bridge and point-of-use citation, not an additional unproved mathematical hypothesis.

The Fourier convention is consistent: \(K_\lambda\) starts with shift \([1]\), Fourier contributes \([1]\), and degree-one cohomology appears as \(H_\lambda[1]\). The constant sign twist has trivial geometric inertia. Conjugate factors use \(H_\lambda^\vee(-1)\); duality reverses the wild phase, and the Tate twist changes no inertia character.

## 2. Fu's hypotheses and the \(\lambda=1\) specialization

[Fu, Proposition 0.8, p. 13, and Theorem 0.1(iii), pp. 5–6](https://arxiv.org/pdf/math/0702436v5) apply over an algebraically closed base field of characteristic \(p>3\). The Kloosterman multiplicative characters are trivial. For the local transform, \(r=3\), \(s=1\), and the required rank-one tame factor is available. The conditions \(s<r\), \(s<p\), and \(p\nmid2rs(s-r)\) all hold.

For \(\gamma(x)=x^3\), \(a(x)=3dx\), differentiation gives
\[
 \xi=-d/x^2,\qquad a(x)+\gamma(x)\xi=2dx.
\]
With \(A=\xi^{-1}\), the resulting pair of phases is
\[
 \pm2\sqrt{A(q-1)^3}.
\]
The quadratic Kummer factor in the theorem is tame; the Gauss factor is unramified. Neither alters this wild coefficient. On \(r_1=t,r_2=zt,t=T^2\), this gives exactly manuscript (6.5):
\[
 \pm\frac{2\sqrt{\alpha/m}}{zT}(\gamma-z)^{3/2},
 \qquad \gamma^3=m/n.
 \tag{3}
\]

At \(\lambda=1\), one \(q\) equals one. That Mackey summand is \([3]_*\mathbf1\), hence tame of rank three; only the other two summands produce wild transforms, totaling rank four. Laumon Theorem 2.4.3(ii) and Proposition 2.5.3.1 give a complete local transform of rank seven, whereas \(H_{\lambda,\eta_0}\) still has rank six. Sequence (2) explains the discrepancy: \(F_1=\operatorname{End}(\mathcal K)\) has a constant direct summand, whose transform is punctual at \(\xi=0\). One trivial quotient is removed in passing from vanishing cycles to generic cohomology. The rank-six generic correlation has four wild dimensions and two tame dimensions. The tame constituents are the two nontrivial cubic Kummer characters, as an unordered pair.

In particular, substituting \(\lambda=1\) into (1) or advertising six wild characters at every unit specialization would be wrong. Neither move is needed in the manuscript. The generic direction has \(\lambda=m/(nz^3)\ne1\), and the constant direction \(z_0\) in Lemma 7.2 explicitly avoids every cubic branch direction (lines 985–1005). Thus these specializations are handled correctly.

## 3. Coincident branches and repeated indices are different cases

For distinct rows \(m\ne m'\) and distinct columns \(n\ne n'\), equal cube-root directions can occur only in opposite entries. Entries in one row would force equal columns; entries in one column would force equal rows. A branch therefore occurs in at most two chosen entries.

Its two possible amplitudes have squares \(4\alpha/m\) and \(4\alpha/m'\). Cancellation of their signed sum would force these squares equal and hence \(m=m'\), which is excluded. This reasoning covers coincident opposite branch sets without a generic-parameter assumption. It also covers every nonempty subset of the four entries (manuscript lines 746–778).

After grouping, a wild coefficient has the form
\[
 \beta(z)=z^{-1}\sum_\gamma c_\gamma(\gamma-z)^{3/2},
 \qquad c_\gamma\ne0.
 \tag{4}
\]
Valuations at the distinct points \(z=\gamma\) prove independence of the squareclasses \(\gamma-z\). The nonzero summands in (4) therefore occupy distinct multiquadratic character spaces and cannot sum to zero. This argument is valid in every characteristic other than two, with no hidden division by the tensor rank.

Genuinely repeated rows or columns do permit constant geometric constituents. For example, a corrected factor tensor its conjugate representative contains the identity line
\[
 \mathbf1(-1)\subset H\otimes H^\vee(-1).
\]
If \(m=m'\), the four-factor product contains two such contractions and hence \(\mathbf1(-2)\). Its Fourier transform is punctual at the origin. This is an actual obstruction to extending off-diagonal punctual exclusion to all unit tuples, but it agrees with the manuscript's repeated-index envelope. Section 6.3 correctly excludes only *nonconstant* linear Artin–Schreier constituents in that case.

## 4. The origin-line argument survives the audit

Suppose a full-support simple constituent is \(J(ar_1+br_2)[2]\) on a dense open, with \(J\) defined over the algebraically closed constant field and \((a,b)\ne(0,0)\). Lemma 7.2, lines 985–1018, chooses a constant ray avoiding all finitely many bad directions. Restricting a lisse inclusion or quotient to its dense open preserves its nonzero rank and induces an actual inclusion or quotient of local representations.

On that constant ray, after the quadratic cover, every wild character is explicitly \(c/Y\), with \(c\) a nonzero constant and \(Y^2=ar_1+br_2\). Thus the passage back to the generic ray uses a fixed constant-field representation; it does not infer a phase from a slope. Any character of this constituent must satisfy
\[
 \beta(z)^2=c^2/(a+bz).
 \tag{5}
\]
Equality on wild inertia suffices: the quotient of two unequal pole-one Artin–Schreier characters remains wild. A Laurent-series coboundary with a pole cannot have only a nonzero pole of order one.

If (4) has at least two groups, its square has nonzero cross terms in distinct pair-character spaces. No two distinct unordered pairs give the same character because the original squareclasses are independent. Since \(p\ne2\), its square is not rational. If there is one group, its square has a zero of order three at \(z=\gamma\ne0\); a nonzero constant divided by a linear function has no finite zero. Both alternatives contradict (5). Multiplicities and tame factors do not affect this argument.

The same exhaustive nonzero list excludes a linear Artin–Schreier constituent, including the constant sheaf: its restriction would be tame at \(T=0\). Fourier equivalence then excludes every punctual constituent in the distinct-index case (Corollary 6.1).

## 5. Nonlinear curves, offset lines, and uniformity

Lemma 7.1's geometric argument was also checked rather than replaced by coefficient covariance. For an irreducible plane curve of degree \(D<p\), the transcendental projection \(h+zk\) is finite of degree \(D\). Its inseparable degree must be one, and every local ramification index is less than \(p\). The manuscript does not incorrectly assume simple tangency.

For a nonlinear curve, the Gauss map is nonconstant: a constant direction would give a vanishing directional derivative, and degree below \(p\) would force a polynomial in one linear form. The Euler derivative is also nonzero on the curve. Otherwise divisibility by its irreducible equation, followed by the distinct homogeneous degrees modulo \(p\), forces a homogeneous binary equation and hence a line.

These facts supply a smooth lisse tangency of the generic projection with nonzero projected value. There the finite pushforward has a nontrivial tame permutation character. Its zero invariant stalk ensures it survives the middle extension. Direct sums of local stationary-phase contributions, rather than numerical trace cancellation, give a nonzero slope-one block at radial infinity. The exact compatibility shift in manuscript (7.3) and the reflection and twist from Fourier inversion do not change this contradiction. The cited Laumon Proposition 2.3.3.1(iii), Theorem 2.4.3(i), and Proposition 2.5.3.1(ii) are the appropriate infinity statements.

For an offset line the representation is a linear Artin–Schreier twist of \(J(v\cdot r)\). A fixed nonzero representation admits at most one linear twist making it tame. Applying \(z\mapsto z+1\) gives equality of two ratios of linear functions, forcing the offset vector parallel to \(v\). This argument remains valid in characteristic \(p\): invariance under translation does not force an arbitrary rational function to be constant, but it does force this degree-one ratio to be constant.

The rank-six local and angular arguments need only \(p>3\). The larger uniform cutoff enters when applying Lemma 7.1 to all possible Fourier-support curves; their degree must first be bounded independently of \(p\) and the unit parameters. That dependency is the previously audited quantitative-complexity construction, not a consequence of rank six.

This focused pass therefore supports the stated constituent exclusions, with bridge (1) now justified. It does not certify the rest of the analytic transfer, and it leaves no permission to replace the distinct-index claim by an all-unit no-punctual claim.
