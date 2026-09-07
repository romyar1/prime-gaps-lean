# Published support and weight inputs for Type III

This audit concerns the citation-edition manuscript
`prime_gaps_20260903/citation_revision_20260904/src/finite_exceptional_type_iii_revised.tex`,
especially its sheaf-facts, pure-core, and weights sections. No manuscript or
foundation source was changed. It distinguishes published general theorems from
calculations still required for the particular correlation family.

The preferred route is the **whole-torus parabolic image followed by coefficient
dilation**. This avoids selecting a possibly noninvariant generic open and avoids
the manuscript's separate curve-to-line lemma. The local calculation excluding
origin-line and origin-point constituents is now a Lean deduction from the
generic laws and supplied local representation data. No cited general theorem
asserts that family-specific exclusion; the actual-family realization remains
an explicit application obligation.

## Verified primary inputs

All weights below use geometric Frobenius and a fixed complex embedding of the
algebraic coefficient field; the Fourier transform has shift `[d]` and no Tate
normalization.

| Input | Primary locator and precise scope |
| --- | --- |
| Trace formula | Deligne, [SGA 4½, *Rapport sur la formule des traces*, Theorem 3.2, p.86](https://publications.ias.edu/sites/default/files/Number32.pdf): separated finite-type schemes over a finite field, constructible characteristic-zero ℓ-adic coefficients, ℓ different from the characteristic. It identifies the point sum with the alternating compact-cohomology trace. Complexes follow by additivity. |
| Weight inequalities and parabolic purity | Deligne, [*Weil II*, §§6.2.2–6.2.4 and Corollary 3.3.6, pp.246–248 and p.206](https://publications.ias.edu/sites/default/files/Number40.pdf). Upper complex weight `v` means ordinary degree `i` has weights at most `v+i`; `Rf_!` preserves upper weights. For smooth `U` and lisse pure weight-`w` coefficients, `im(H_c^i(U,F) → H^i(U,F))` is pure weight `w+i`. The latter directly supplies the core's purity. |
| Perverse support and intermediate extension | BBD, [*Faisceaux pervers*, Corollaries 1.4.24–1.4.25, §2.2, Theorem 4.3.1, Corollary 5.3.2, Theorem 5.3.8](https://publications.ias.edu/sites/default/files/Faisceaux%20pervers.pdf). These give the strict boundary condition, finite length/simple intermediate extensions, purity of affine intermediate extension, and geometric semisimplicity of pure perverse sheaves. Proposition 2.2.4 is stated first in the classical setting; use the étale recollement/t-structure developed in §§2.2.9–2.2.18 for the present application. |
| Fourier equivalence and functoriality | Laumon, [*Transformation de Fourier…*, Theorem 1.2.2.1, Corollary 1.2.2.3, Theorem 1.2.2.4, Proposition 1.2.2.9, Theorem 1.3.2.3 and Corollary 1.3.2.4](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf). For vector bundles over the permitted characteristic-`p` bases and nontrivial additive character, Fourier is a perverse equivalence, preserves simplicity, commutes with base change, and intertwines linear maps with their transposes. Here finite or algebraically closed ground fields meet §0.6's finiteness condition. Inversion is `FT_d²(P) ≅ [-1]*P(-d)`. |
| Fourier purity | Katz–Laumon, [*Transformation de Fourier et majoration de sommes exponentielles*, Theorem 2.1.3, Corollary 2.1.5, Theorem 2.2.1, pp.154–155](https://www.numdam.org/article/PMIHES_1985__62__145_0.pdf). The original forget-support map `FT_! → FT_*` is an isomorphism. Over a finite-field base, the shifted rank-`d` Fourier transform takes pure weight `v` to pure weight `v+d`. This requires no assertion about the support of its simple factors. |
| Whole-base lissity from conductors | Laumon, [*Semi-continuité du conducteur de Swan*, §2.1, Theorem 2.1.1(ii), Corollary 2.1.2 and Remark 2.1.3, pp.185–187](https://www.numdam.org/article/AST_1981__82-83__173_0.pdf). Hypotheses: excellent Noetherian base, separated smooth relative curve, finite flat deleted boundary, and finite-coefficient lisse sheaf of constant rank. Local constancy of the sum of boundary Swan conductors plus ranks gives universal local acyclicity of zero extension; proper compactification gives lisse direct images. |
| Complexity, degrees, and Betti numbers | Sawin–Forey–Fresán–Kowalski, [*Quantitative sheaf theory*](https://arxiv.org/pdf/2101.00635v4): Theorem 6.8 controls six operations for embedded quasi-projective varieties; Theorem 6.15 and Corollary 6.16 control constituents/intermediate extension; Proposition 6.21 controls fixed-degree graphs; Theorem 6.23 controls nonlisse-locus degrees on an irreducible ambient variety; Proposition 6.24 bounds ordinary-cohomology complexity by a possibly nonexplicit function `N(n,c)`; Proposition 7.1 bounds Betti numbers; Proposition 7.18 bounds Fourier complexity. Corollary 7.4 and Proposition 7.5 handle the starting curve/Artin–Schreier sheaves. These bounds are uniform in characteristic and coefficients at fixed complexity. |
| Actual Kloosterman coefficient scaling | Katz, [*Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Theorem 4.1.1 and Lemma 4.1.9, pp.48–53](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf). Changing `ψ(x)` to `ψ(a x)` scales the argument by `a^(Σb_i)`, possibly after a specified finite extension. For rank three, `b_i=1` and all multiplicative characters trivial, that extension degree is one. Thus the normalized sheaf satisfies the arithmetic isomorphism `τK ≅ [8]*K` for `τ(ζ_p)=ζ_p²`. |
| Stationary phase and explicit local transforms | Laumon, [Proposition 2.3.3.1(iii), Theorem 2.4.3, Proposition 2.5.3.1(ii)](https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf), and Fu, [*Calculation of ℓ-adic local Fourier transformations*, Proposition 0.8 and Theorem 0.1(iii)](https://arxiv.org/pdf/math/0702436v5). Fu's application here has `r=3,s=1`, hence `p>3`. The finite-origin bridge additionally uses Laumon §2.3.2, Proposition 2.3.2.1(iii), and Lemma 2.4.2.1(ii). The geometric phase-exclusion argument is a further family-specific deduction. |

## Whole-torus core: the exact deduction required

Write `S = Gm_λ × Gm_ξ`, `V = Gm_x × S`, `f : V → S`, and

```
F = K(x) ⊗ K(λx)^∨ ⊗ Lψ(ξx),
Hpar = im(R¹f_!F → R¹f_*F).
```

The boundary of `P¹ × S` consists of two sections. The actual input and its
dual have rank nine, `Swan_0=0`, `Swan_∞=9`, so the conductor sum is
`(9+0)+(9+9)=27` for every unit pair, including `λ=1`. The finite-coefficient
conductor theorem applies. Passing to a stable lattice and its finite reductions
is necessary: wild inertia has finite prime-to-ℓ image, so averaging preserves
its invariant dimensions on reduction; successive extensions and inversion of ℓ
give the ℓ-adic statement. This is a deduction, not the literal coefficient
scope of the 1981 theorem.

The compact direct images are lisse. Relative duality supplies
`R¹f_*F ≅ (R¹f_!F^∨)^∨(-1)` and its base change; see the whole-base case in
the proof of QST Theorem 6.27, Step 1, citing SGA 4½ *Th. finitude* 2.1.
Images of morphisms of lisse sheaves remain lisse, and exact stalk pullback
identifies this image with the parabolic cohomology image in each fiber.

The rank calculation is separate: compact `H¹` has dimension nine; the zero
boundary invariants have dimension three and inject into it; infinity has no
invariants. The image has rank six. Its weight is one by Deligne's image-purity
corollary. For the constant Weil sign sheaf `ε` with `Frob_p=-1`, set
`H=ε⊗Hpar`. At `q=p^d`, the correct identity is

```
t_H(λ,ξ; F_q) = (-1)^(d+1) (C_q(λ,ξ) + 1 + q⁻¹ + q⁻²).
```

The prime-field identity is positive; the all-extension identity is not
unsigned. The conjugate factor is `H^∨(-1)`. Full justification of the rank,
boundary eigenvalues and trace identification uses the actual Kloosterman local
representation, not conductor constancy alone. See the more detailed
[whole-torus note](../geometry/relative_core_lissity.md).

## Generic support laws sufficient for coefficient dilation

These are consequences of the coefficient and perverse formalism, not additional
assertions about this family:

1. A continuous coefficient-field automorphism induces an exact equivalence,
   commuting with ordinary cohomology, stalks, tensor products, duals and the
   six operations. Nonzero stalks and their dimensions are preserved.
2. It preserves the perverse t-structure; so does pullback by a scheme
   isomorphism. Both preserve simple objects and transport Jordan–Hölder
   multisets. Pullback transports support by inverse image.
3. Intermediate extension is characterized by absence of boundary subobjects
   and quotients. The preceding equivalences therefore commute with it.

Coefficient restriction is an actual equivalence of module categories here;
perverse exactness follows from the stalk/costalk definitions. BBD §§2.2.16–18
and §4.0 provide the coefficient framework. No claim that coefficient
automorphisms preserve a chosen complex absolute value is used.

For the concrete calculation take `E=Q₂(ζ_p)` and its unramified automorphism
`τ(ζ_p)=ζ_p²`. Put

```
b(λ,ξ) = (λ,ξ/4),           a(x,λ,ξ) = (8x,λ,ξ/4),
φ_mn(r₁,r₂) = (m r₁³/(n r₂³), m r₁²/(αr₂)),
s_c(r₁,r₂) = (c r₁,c r₂).
```

The identities `f∘a=b∘f`, `τF≅a*F`, and
`φ_mn∘s_(1/4)=b∘φ_mn` give `τH≅b*H` and, for each tensor subproduct,
`τG≅s_(1/4)*G`. The same holds for dual-twisted factors. Use the canonical
torus inclusion in `P=j_!*(G[2])`. With `Q=FTψ(P)`, changing variables `r=4u`
gives

```
τQ ≅ FTψ₂(s_(1/4)*P) ≅ s_8*Q.
```

There is no new Tate twist or sign. This is a calculation with the actual
sheaves and maps, not a published theorem whose statement is this isomorphism.

Consequently the **union** of proper geometric constituent supports is
`s_8`-invariant; individual constituents may be permuted. Its curve part has a
bounded-degree defining polynomial, and its punctual part has bounded
cardinality. For `p>8^D`, the already proved radial-polynomial argument puts
the curve part in finitely many origin lines; the finite orbit argument puts
the punctual part at the origin. `TypeIIIPublishedFourierRules` then excludes
the proper constituents in the distinct case from its local phase hypotheses.
See [the support-rigidity proof](../geometry/cyclotomic_support_rigidity.md).

## From full support to the numerical weights

For a product of `w` rank-six weight-one factors, `P` has weight `w+2` and
`Q` weight `w+4`. If all simple factors of `Q` have full surface support,
the strict boundary condition gives

```
H^i(Q)=0 for i∉{-2,-1},       dim Supp H⁻¹(Q)≤0.
```

Hence the eigenvalue bounds are `q^((w+2)/2)` in degree `-2` and
`q^((w+3)/2)` in degree `-1`. A uniform complexity bound controls stalk
dimensions by point pullback. For the finite-support sheaf `M=H⁻¹(Q)`,
`|Supp M| ≤ Σ_z dim M_z ≤ c(M)`, and Proposition 6.24 bounds the last
quantity uniformly. Nonexplicit constants suffice. Mere perversity, or full
support of the whole object, does not imply this conclusion: a curve-supported
simple factor would contribute in degree `-1`.

## Invocations that would be invalid

- QST Theorem 6.27 only supplies a dense open. It does not give whole-torus
  base change, nor does an arbitrary chosen open automatically respect dilation.
- Bounded rank does not imply bounded complexity or bounded exceptional degree.
- Equality/covariance of traces over `F_p` alone does not identify geometric
  sheaves or their supports. The finite-sum covariance alone does not prove
  invariance of perverse supports. `TypeIIIPublishedCovarianceRules` additionally
  uses all-extension trace identification, geometric semisimplicity and
  intermediate extension in its precise Chebotarev hypothesis.
- Coefficient conjugation does not preserve absolute values. For example,
  `ζ₅+ζ₅⁻¹` and its `ζ₅↦ζ₅²` conjugate have different magnitudes. Thus norm-defined
  exceptional sets need not be dilation-invariant.
- Six wild dimensions describe generic `λ≠1`; at `λ=1` the rank-six core can
  contain four wild and two tame dimensions. Neither generic stationary phase
  nor purity alone excludes the residual origin supports.

The general inputs above are explicit Lean hypotheses. The rank/trace linear
algebra, covariance and proper-support exclusion have separate checked
deductions. The family's actual cohomology and local representations, its
lissity/purity applications and uniform complexity still have to instantiate
the supplied data. The resulting Type III theorem is conditional on those
inputs; this audit does not discharge them.
