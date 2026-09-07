# Proper affinization and the missing fiber step

Let `q : X → Spec R` be proper and put `A = Γ(X, O_X)`. The formal
construction uses the original maps

\[
X \xrightarrow{h=\operatorname{toSpec}\Gamma}
\operatorname{Spec} A \xrightarrow{g} \operatorname{Spec} R.
\]

The coefficient map defining `g` is the original map on global sections,
with the canonical identification of `R` with the global sections of
`Spec R`. The equality `h ≫ g = q`, integrality of `g`, and properness and
surjectivity of `h` are proved in
[`TypeIIIProperAffinization.lean`](../../../formal/TypeIIIProperAffinization.lean).
The original structure map `O_(Spec A) → h_* O_X` is an isomorphism by
[`TypeIIIProperAffinizationStructureSheaf.lean`](../../../formal/TypeIIIProperAffinizationStructureSheaf.lean).
Its proof uses localization on basic opens and detection of a sheaf
isomorphism on that basis. The structure-sheaf statement already holds
for every quasi-compact, quasi-separated `X`.

The actual map on clopens is also an order isomorphism. It follows from
the global-idempotent correspondence proved in
[`TypeIIISchemeIdempotentClopens.lean`](../../../formal/TypeIIISchemeIdempotentClopens.lean).
These assertions concern the original schemes and morphisms; no
connectedness of the fibers is included.

## What connected fibers require

For a proper morphism `f : Y → S` and `s ∈ S`, the additional result is
that every idempotent in `Γ(Y_s, O_(Y_s))` belongs to the image of

\[
(f_*\mathcal O_Y)_s\longrightarrow\Gamma(Y_s,\mathcal O_{Y_s}).
\]

The lift in the stalk need not itself be idempotent. This is
[Stacks, Lemma 36.32.7 (0G7X)](https://stacks.math.columbia.edu/tag/0G7X).
It is not yet a proved theorem of this development.

For the surjective affinization map above, this image statement and
`h_* O_X = O_(Spec A)` give connected fibers: the image of a stalk section
in a fiber factors through the residue field, whose only idempotents are
zero and one. Flat base change of global sections gives the corresponding
geometric connectedness statement. This is the remaining step in the
[Stacks proof of Stein factorization (03H2)](https://stacks.math.columbia.edu/tag/03H2).

The completed henselian-algebra lifting theorem controls
`A → A/mA`. It does not identify `A/mA` with `Γ(X_s, O_(X_s))` and does
not imply that the latter ring's idempotents lie in the image. In
particular, integral-algebra clopen lifting alone does not establish
clopen lifting from a proper nonaffine closed fiber.

## The degree-zero formal-functions route

Over a Noetherian local base with maximal ideal `m`, write
`Y_n = Y × Spec(R/m^(n+1))`. Their underlying spaces agree with the closed
fiber. Its clopen decomposition therefore specifies compatible
idempotents on the infinitesimal fibers. The actual infinitesimal schemes,
transitions, and unique compatible family of idempotents are proved in
[`TypeIIIInfinitesimalIdempotentTower.lean`](../../../formal/TypeIIIInfinitesimalIdempotentTower.lean),
for an arbitrary ideal and without properness or Noetherianity.
The degree-zero case of
[formal functions, Stacks 02OD](https://stacks.math.columbia.edu/tag/02OD),
identifies the inverse limit of those global-section rings with the
completion of the original global-section module. The canonical map is
now constructed in
[`TypeIIIInfinitesimalCompletion.lean`](../../../formal/TypeIIIInfinitesimalCompletion.lean).
Its coordinates use the original completion evaluations and the
original restrictions to the actual infinitesimal schemes. Compatibility
with every transition and with original global sections is proved. Its
construction requires neither properness nor Noetherianity.

For affine `X`, the original restriction is surjective and has kernel
`I^(n+1)Γ(X)`. This is proved from the actual affine pushout of section
rings in
[`TypeIIIInfinitesimalAffineSections.lean`](../../../formal/TypeIIIInfinitesimalAffineSections.lean).
It makes the same completion map a linear equivalence in
[`TypeIIIInfinitesimalAffineCompletion.lean`](../../../formal/TypeIIIInfinitesimalAffineCompletion.lean),
without a finite-generation assumption. The original compatible
idempotent family has a completed preimage in this case. Surjectivity
of this map for a general proper scheme remains unproved.

The final algebraic step uses the original evaluation from the completion
modulo `m`: for a finitely generated ideal, completion has the same
quotients by its powers. See
[Stacks, Lemma 10.96.3 (05GG)](https://stacks.math.columbia.edu/tag/05GG).
Pinned Mathlib already proves the needed algebra: `AdicCompletion.eval`
and `eval_comp_of` are the original evaluation and quotient maps;
`eval_surjective` requires no finite-generation hypothesis, and
`pow_smul_top_eq_ker_eval` proves the kernel equality assuming only that
the ideal is finitely generated. These are in
`Mathlib/RingTheory/AdicCompletion/Basic.lean` and `Completeness.lean`.
That step moves the completed section back into the image of the original
section map. The general algebraic range equality for the original
linear map is proved in
[`TypeIIIAdicCompletionRangeDescent.lean`](../../../formal/TypeIIIAdicCompletionRangeDescent.lean).
The geometric specialization now proves that a completed preimage of
the actual idempotent family gives an original section with its
prescribed closed-fiber value. It does not assert that this original
section is idempotent.

A narrower way to obtain the required value is eventual equality of
the images `Γ(Y_k) → Γ(Y_0)` and `Γ(Y) → Γ(Y_0)`. The degree-zero case of
[Stacks 02OB(3)](https://stacks.math.columbia.edu/tag/02OB) proves this for
proper schemes over a Noetherian base. Applying it to a sufficiently high
coordinate of the already constructed family would suffice; full
bijectivity of the completion comparison is stronger than needed.
The proof still requires finite generation of the graded cohomology
modules over the Rees algebra, in particular in degree one; see
[Stacks 02O8](https://stacks.math.columbia.edu/tag/02O8). The pinned
Artin–Rees results do not supply this geometric finiteness theorem.
Finite-type affine charts need not have section modules finite over
the base, so applying Artin–Rees directly to their Čech terms would
leave an unjustified hypothesis. The map from the pulled-back Rees
algebra to the powers of the ideal sheaf is a surjection; equality is
not available without an additional flatness argument.

The general proper case in 0G7X also requires proper Noetherian
approximation. Given a cofiltered limit of qcqs schemes with affine
transition maps,
[`TypeIIIAffineLimitIdempotentDescent.lean`](../../../formal/TypeIIIAffineLimitIdempotentDescent.lean)
now proves that the original global idempotents and clopens descend to
a stage, and equal representatives agree at a common later stage. This
uses the original limit projections. It supplies the idempotent-descent
step once the proper Noetherian diagram is constructed; construction
of that diagram remains unproved. No formal-functions, graded-cohomology
finiteness, or approximation assertion is introduced as an axiom or
substituted for the Type III target.

There is also an elementary checkpoint for the projective-plane route.
[`TypeIIIHomogeneousCoordinateIntersection.lean`](../../../formal/TypeIIIHomogeneousCoordinateIntersection.lean)
proves that, for distinct variables and homogeneous polynomials of
degrees `n` and `m`, an equality `P X_j^m = Q X_i^n` forces a unique
common scalar: `P = r X_i^n` and `Q = r X_j^m`. This works over every
commutative ring, including rings with nilpotents and the zero ring,
and permits zero exponents. Applying it to the original projective
chart restrictions still requires denominator clearing and gluing.
The bijectivity of the original map `R → Γ(P²_R,O)` has not yet been
proved here; even that bijectivity would not supply the needed
cohomological finiteness for finite covers of the projective plane.

Proper étale base change, the adic and trace comparisons, and the uniform
local Fourier estimate remain further requirements. The verified
affinization statements above do not discharge them.
