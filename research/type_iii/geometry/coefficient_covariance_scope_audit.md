# Scope audit: coefficient covariance and exceptional supports

Date: 4 September 2026.

The new Lean identities are sound at their stated scope. They prove invariance of the zero and nonzero sets of the actual prime-field Fourier values. They do not identify an invariant geometric exceptional support, and they do not preserve a set defined by a complex absolute-value threshold. Neither missing inference can be supplied by finite cardinality or purity alone.

This note reviews the frozen sources [TypeIIICoefficientCovariance.lean](../../../formal/TypeIIICoefficientCovariance.lean), [TypeIIIScalingSupport.lean](../../../formal/TypeIIIScalingSupport.lean), and [TypeIIIScalingLines.lean](../../../formal/TypeIIIScalingLines.lean). It introduces no new formal hypotheses and changes no manuscript.

## The exact arithmetic conclusion

Write \(F(h,k)\) for the actual four-cycle transform defined in TypeIIILocal, including its prescribed zero extensions. For every prime \(p\) and every \(a\in\mathbf F_p^\times\), the theorem exists_fourCycle_fourier_coefficient_automorphism constructs one field automorphism \(\sigma_a\) of \(\mathbf C\) such that
\[
 \sigma_a(\psi(t))=\psi(at),\qquad
 \sigma_a(F(h,k))=F(a^3h,a^3k).
\]
The automorphism is chosen before all row, column, physical, and Fourier parameters. The four row and column parameters must be nonzero; no distinct-index hypothesis or nonzero hypothesis on \(\alpha\) is needed for this endpoint.

Consequently
\[
 F(h,k)=0\quad\Longleftrightarrow\quad F(a^3h,a^3k)=0.
\]
This is the separately proved theorem fourCycle_fourier_zero_iff_cubic_dilation. Thus both the numerical zero set and its complement in \(\mathbf F_p^2\) are stable under every scalar in \((\mathbf F_p^\times)^3\). In particular, they are stable under multiplication by eight when \(p>2\). Rational algebraic relations among simultaneously transformed values are also preserved.

The values lie in the cyclotomic field \(\mathbf Q(\zeta_p)\), where the automorphism has its prescribed canonical restriction. Extending it to \(\mathbf C\) does not assert continuity or preservation of absolute values. The conjugate Kloosterman factors are handled through their explicit finite-sum identities; the proof does not assume that an arbitrary complex field automorphism commutes with complex conjugation.

Only \(\mathbf F_p\)-points are quantified. There is no assertion about stalks, geometric points, extension-field traces, support dimensions, or a polynomial of uniformly bounded degree containing a support.

## What the polynomial endpoints require

For any field \(K\) of characteristic \(p\), the scaling modules establish the following actual algebraic results.

* If \(Z\subset K^2\) is finite, \(|Z|\le D\), \(bZ\subset Z\), \(b>1\), and \(b^D<p\), then \(Z\subset\{0\}\).
* If \(Y\subset K^2\) satisfies \(bY\subset Y\) and is contained in the zero locus of a nonzero polynomial \(f\) of total degree at most \(D\), with the same cutoff, then \(Y\) is covered by at most \(D+1\) proper lines through the origin.

The second statement is invariant_subset_line_cover_of_cutoff. For \(z\in Y\), the polynomial \(f(tz)\) has the \(D+1\) distinct roots \(1,b,\ldots,b^D\), so every homogeneous component of \(f\) vanishes at \(z\). Dehomogenizing the nonzero top component supplies the finite line cover. The containing zero locus need not be invariant, and this argument does not require algebraic closure.

For a geometric application, both set invariance and a bound \(D\) independent of \(p\) and the residue parameters must refer to the actual geometric set. Neither input follows from numerical covariance. Taking the Zariski closure of finitely many \(\mathbf F_p\)-samples, or interpolating their values, does not supply the required uniform degree bound. A closed irreducible curve contained in this finite line cover is one of its lines; this last geometric interpretation is separate from the stated Lean containment theorem.

## Two invalid inferences, with counterexamples

### Complex covariance does not preserve a norm exception

Let \(\zeta=\exp(2\pi i/5)\) and \(u=\zeta+\zeta^{-1}\). Then
\[
 u=\frac{\sqrt5-1}{2},\qquad
 \sigma_2(u)=\zeta^2+\zeta^{-2}
            =-\frac{\sqrt5+1}{2}.
\]
Hence \(|u|<1<|\sigma_2(u)|\). Both values are real, and cyclotomic conjugation commutes with complex conjugation on this field. These additional facts do not give equal absolute values. In particular, covariance cannot by itself show invariance of
\[
 E_C=\{(h,k): |F(h,k)|>Cp^3\}.
\]

Even an independently bounded cardinality of \(E_C\) does not repair the inference. Here is an exact auxiliary example with the same cubic covariance. Set \(p=101\), \(\zeta=\exp(2\pi i/101)\), and
\[
 u=\sum_{j=-25}^{25}\zeta^j,\qquad
 \tau_a(\zeta)=\zeta^a.
\]
Define a real cyclotomic-valued function on \(\mathbf F_{101}^2\) by
\[
 G(h,0)=101^2\tau_{h^{67}}(u)\quad(h\ne0),\qquad
 G(h,k)=0\quad\text{otherwise}.
\]
Since \(3\cdot67\equiv1\pmod{100}\),
\[
 \tau_a(G(h,k))=G(a^3h,a^3k)
\]
for every \(a\ne0\). For integer representatives \(1\le a\le100\),
\[
 |\tau_a(u)|
 =\frac{|\sin(51\pi a/101)|}{\sin(\pi a/101)}.
\]
At \(a=\pm1\) this is \(1/(2\sin(\pi/202))>101/4\). At every other \(a\), the denominator is at least \(\sin(2\pi/101)>4/101\), so the value is less than \(101/4\). Therefore
\[
 \{z:|G(z)|>101^3/4\}=\{(1,0),(-1,0)\}.
\]
This two-point set is not stable under multiplication by eight, although \(101>8^2\). This is a counterexample to an inference from the symmetry, not to the particular Type III estimate.

### One-field traces do not determine geometric support

Fix \(p>7\), an auxiliary prime \(\ell\ne p\), and the closed line
\[
 C=\{(h,k):h=1\}\subset\mathbf A^2_{\mathbf F_p}.
\]
On \(C\), let \(E\) be the sum of two geometrically constant rank-one Weil sheaves whose Frobenius eigenvalues are \(1\) and \(-1\). With \(i:C\hookrightarrow\mathbf A^2\), set \(Q=i_*E[1]\).

The complex \(Q\) is a pure perverse sheaf of weight one, with bounded rank and complexity. Its trace at every \(\mathbf F_p\)-point is zero: on \(C\) the alternating trace is \(-(1-1)=0\), and off \(C\) its stalk is zero. Its trace function therefore satisfies every cubic coefficient-covariance identity trivially. Nevertheless,
\[
 \operatorname{supp}\mathcal H^{-1}(Q)=C,
\]
which is not stable under multiplication by eight. Over \(\mathbf F_{p^2}\), its trace on \(C\) is \(-2\).

Thus even purity and bounded complexity do not turn an identity of traces over one finite field into invariance of ordinary cohomology support. This example also prevents identifying the numerical nonzero set with the support of a cohomology sheaf. It is again an obstruction to an inference, not a counterexample to the actual corrected correlation sheaf.

## The independent geometric argument still needed

The proposed route in [cyclotomic_support_rigidity.md](cyclotomic_support_rigidity.md) uses an isomorphism of sheaves constructed by changes of variables. It must remain logically separate from the new complex-valued theorem.

One can work with \(\ell=2\) and odd \(p\), using a continuous coefficient automorphism \(\tau\) of \(\overline{\mathbf Q}_2\) with \(\tau(\zeta_p)=\zeta_p^2\). This uses the unramified local-field construction and a Frobenius lift; for a fixed \(\ell\), an arbitrary cyclotomic automorphism is not automatically available as a continuous \(\mathbf Q_\ell\)-automorphism. [Milne, Algebraic Number Theory, Proposition 7.50, Corollary 7.51, and Example 7.54](https://www.jmilne.org/math/CourseNotes/ANT.pdf) give the relevant unramified-extension and roots-of-unity statements.

For each actual nonempty corrected-core tensor product, construct the required input complex \(P\), with its specified extension from the torus, and establish
\[
 \tau P\simeq s_{1/4}^{*}P,\qquad
 s_c(r_1,r_2)=(cr_1,cr_2).
\]
This requires coefficient change to commute with the actual direct images, their rank-six image, duality and twists, and the chosen intermediate extension. It is not obtained by comparing only prime-field traces. A relative change of variables in the Kloosterman and correlation constructions is the concrete proposed source of this isomorphism.

For \(Q=\operatorname{FT}_{\psi}(P)\), Fourier functoriality then gives
\[
 \tau Q
 \simeq \operatorname{FT}_{\psi_2}(s_{1/4}^{*}P)
 \simeq s_8^{*}Q.
\]
The substitution is \(r=4u\), and the phase becomes \(2(4u\cdot\eta)=u\cdot8\eta\). For this isomorphism of equal-dimensional vector spaces there is no extra shift or Tate twist. The relevant Fourier change-of-variables and base-change statements are [Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de Weil, Theorem 1.2.2.4 and Proposition 1.2.2.9](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf).

An established isomorphism of this kind does preserve stalk dimensions and yields eight-invariance of each ordinary cohomology support, of the union of supports of all geometric dimension-one simple perverse constituents, and of the union of punctual constituent supports. Individual constituents may be permuted. No equality of complex norms is used.

Uniform bounds for these actual sets remain a separate geometric input. The pertinent tools are the constituent, ordinary-cohomology, stratification, and Fourier complexity bounds in [Quantitative sheaf theory, Theorems 6.15 and 6.23, Proposition 6.24, Lemma 6.26, and Proposition 7.18](https://arxiv.org/pdf/2101.00635v4). Their application must control the actual family uniformly in every allowed residue-parameter specialization; rank alone is insufficient.

With these connections established, the frozen algebraic endpoints give origin support for the finite sets and an origin-line cover for the curve sets. The remaining Type III proof still needs the actual core trace realization, the full local character calculation to exclude those lines, and the purity, Fourier, and weight estimates that yield cancellation before raw-kernel restoration. The six wild radial characters are a generic-\(\lambda\) description; \(\lambda=1\) has a tame remainder and cannot be silently included in that description. If an extension-field trace comparison is used, the corrected-core unramified sign twist must also be retained: over \(\mathbf F_{p^r}\), its signed normalized trace is \((-1)^{r+1}(C_{p^r}+\kappa_{p^r})\).

No flaw was found in the three frozen modules' stated algebraic conclusions. The unjustified step would be to promote their prime-field numerical covariance to either geometric-support invariance or norm-exception invariance without the independent inputs above.
