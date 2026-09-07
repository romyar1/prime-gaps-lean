# The additive-character sheaf construction

This note records the geometric input actually constructed in Lean. It does
not assert the Type III local Fourier proposition.

Let `R` be a commutative ring of prime characteristic `p`, and let `f∈R`.
The development uses the literal algebra

```text
A = R[X]/(X^p−X−f).
```

Its defining polynomial is monic of degree `p` and has derivative `−1`.
The formal construction supplies a basis, proves that `A` is finite free
and étale over `R`, and proves that `Spec A→Spec R` is surjective. It is
therefore an actual covering in the small étale site. The translations
`τ_a(X)=X+a`, for `a∈F_p`, act on the cover.

The torsor statement is an explicit algebra isomorphism

```text
A ⊗_R A ≃ ∏_{a∈F_p} A,       x ⊗ y ↦ (x τ_a(y))_a.
```

It is also proved on schemes: the self-pullback of the cover is the
coproduct of `p` copies, with projections the identity and the corresponding
deck transformation. The proof works for rings with zero divisors. Quotient
formation commutes with arbitrary algebra base change.

Let `E` be a commutative coefficient ring in which `p` is invertible, and
let `ψ:F_p→E` be an additive character. The ambient module sheaf is the
sheafification of the free module presheaf on the representable cover.
The character sheaf is the image of the sheafified average

```text
P = p⁻¹ ∑_a ψ(a)·τ_a.
```

Its geometric stalk at a compatible point `R→K→Ω`, with `Ω` algebraically
closed, is linearly equivalent to the character submodule on the actual
roots of the specialized polynomial:

```text
{v : {z∈Ω | z^p−z=f(K)} → E | ∀a,z, v(z+a)=ψ(a)v(z)}.
```

Evaluation at any root identifies this submodule with `E`; algebraic
closedness supplies a root. Sheafification, the point fiber, the free-module
comparison, and preservation of the image all enter through proved
isomorphisms. Freeness and rank one are conclusions of this construction;
the coefficient ring is allowed to have zero divisors.

The signs arise from the distinction between a point permutation and its
action on basis coefficients. Sending a basis vector at `z` to the one at
`z+a` makes its coefficient function become `v(z−a)`. Consequently, the
positive-weight sheaf average above corresponds to the function projector
`p⁻¹∑_a ψ(−a)v(z+a)`.

The average is also proved idempotent as a morphism of the actual sheaf.
Its image inclusion has a retraction given by the categorical factorization
through the image. The identity section of the cover gives a section of the
free sheaf; projecting it gives a section of the character sheaf. On the
covering object, this section defines a map from the categorical constant
sheaf `E`. In the function description, its value at the chosen root is
the unit `p⁻¹`. Multiplying root evaluation by `p` gives an explicit inverse
to the induced stalk map. This proves that the map is an isomorphism at
every geometric point, including with torsion coefficients. The
construction proves the slice-site comparisons and an actual
conservative family of algebraically closed points, so these stalk
isomorphisms imply the sheaf isomorphism

```text
character sheaf restricted to Spec A ≅ constant sheaf E.
```

Thus local triviality is a theorem about this sheaf on this actual cover.
It requires no chosen roots on the original base. For a coefficient field,
invertibility of `p` is equivalent to `(p:E)≠0`; the ring average and image
are proved to agree with the field constructions in that case.

For finite `K`, arithmetic Frobenius sends a root to
`z^|K|=z+Tr_{K/F_p}(f(K))`. Geometric Frobenius is its inverse. Its action on
the actual sheaf stalk is induced by that automorphism of the geometric
point, before any character-space comparison is made. On coefficient
functions it therefore acts by `v(z+Tr(f(K)))`. The proved trace is

```text
tr(Frob_geom | character stalk) = ψ(Tr_{K/F_p}(f(K))).
```

The trace is taken on the actual stalk after its finite freeness has been
proved. The formula holds for the commutative coefficient rings just
described.

For the standard complex character this is exactly
`FiniteFieldSums.traceAddChar p K (f(K))`; over `F_p` it is
`ZMod.stdAddChar (f(F_p))`.
The trace theorem assumes `Ω` is algebraically closed and algebraic over
the finite field `K`, with compatible prime-field algebra structures.

The map `R→K` may have a nonzero kernel. The cover fiber, its free module,
the actual image-sheaf stalk, and the point-induced Frobenius all retain
the original affine base throughout these comparisons.

## Finite coefficients and their inverse limit

For distinct primes `p,ℓ`, the actual coefficient levels are

```text
Λ_n = (Z/ℓ^(n+1))[X]/Φ_p(X),       n ≥ 0.
```

The development proves a basis of length `p−1`, exact characteristic
`ℓ^(n+1)`, cardinality `ℓ^((n+1)(p−1))`, and invertibility of `p`.
The image of `X` is a primitive `p`th root of unity. It defines an actual
primitive additive character `ψ_n:F_p→Λ_n`. For every `m≤n`, the quotient
map `Λ_n→Λ_m` is constructed and proved surjective; these maps respect the
roots and characters and satisfy the identity and composition laws.
Specializing the character-sheaf construction to each `Λ_n` gives an
actual locally trivial sheaf. Its geometric Frobenius trace is
`ψ_n(Tr(f(K)))`, and these traces commute with reduction.

The transition maps are also constructed on the sheaves themselves.
For a coefficient homomorphism respecting the characters, the map on
free generators extends through the actual sheafification and intertwines
the averaging projectors. Inclusion into the ambient sheaf, this
coefficient map, and the actual target retraction give the map between
the character images. Its image-inclusion square and its identity and
composition laws are proved. Applying this to the cyclotomic reductions
and forgetting to additive sheaves gives a functor from `N` with its
order reversed to sheaves on the original small étale site. This proves
coherence of the actual transition maps.

Extension of scalars is the sheafification of the ordinary tensor-product
functor. Its canonical map from the extended character sheaf to the target
character sheaf is proved to be an isomorphism. The proof first identifies
the actual free sheaves under extension of scalars, then transports their
split character projectors. It identifies the adjoint of this isomorphism
with the coefficient map already constructed above. No flatness assumption
is needed: the images in question are actual split images. In particular,
for each `m≤n`, extension of scalars from `Λ_n` to `Λ_m` gives the original
level-`m` sheaf with its original transition map.

The ring `Λ` is the subring of `∏_n Λ_n` consisting of compatible
sequences. Coordinate projection and the lift of every compatible family
of ring homomorphisms satisfy the inverse-limit universal property.
The roots, characters, and inverses of `p` form compatible sequences;
primitivity is detected by the projection to `Λ_0`.

Giving each finite level the discrete topology and `Λ` the product
subspace topology makes `Λ` a compact Hausdorff, totally disconnected
topological ring. Closedness follows by writing compatibility as the
intersection of the actual reduction equalizers. The projections and
the lift of any compatible continuous family are continuous. These
constructions do not choose a local factor of `Λ` or identify it with a
coefficient field.

The existing finite monomial bases commute with reduction. Their
compatible coordinates lift to `Z_ell` using actual Cauchy sequences of
integer representatives. This proves a linear equivalence

```text
Λ ≃ (Z_ell)^(p−1),
```

whose inverse takes a vector `(a_i)` to `∑_i a_i ζ^i` in the original
limit ring. The scalar homomorphism `Z_ell→Λ` is constructed from its
actual finite projections. This is a module equivalence, not a
product-ring decomposition. Every finite projection is surjective, and
its kernel is exactly `(ell^(n+1))`: vanishing is equivalent to divisibility
of every lifted coordinate by that power. Consequently the canonical
quotient equivalence `Λ/(ell^(n+1)) ≃ Λ_n` commutes with the original
projection.

These projection kernels form a decreasing neighborhood basis for the
original product-subspace topology. Their computed kernels prove that
this topology is the `(ell)`-adic topology. The ring is Noetherian by its
actual finite module structure over `Z_ell`, and compactness and
Hausdorffness prove completeness and separation for the same ideal.
These coefficient-ring results require both primes but allow `p=ell`.
The character-sheaf construction still requires `p≠ell`.

Over `Λ` itself, the original character-image construction gives an
ordinary module sheaf, trivialized by the same cover. Its canonical
tensor extension to `Λ_n` is the original finite sheaf. All finite levels,
restricted along their original projections, form an inverse system
of `Λ`-module sheaves. The limit-coefficient sheaf has a compatible cone
to this system. No theorem here identifies that cone as a categorical
limit or compares ordinary `Λ`-sheaf cohomology with adic cohomology.

## Exact extension by zero

For a monomorphic étale map `j:U→S`, the development constructs the
actual left adjoint `j_!` to restriction between the small étale sites.
Before sheafification, its value on an object `V` is the coproduct of the
given presheaf values indexed by maps `V→U` over `S`. The explicit
coproduct maps establish the left Kan extension universal property.

The geometric stalk of `j_!F` is the corresponding stalk of `F` at a
point in `U` and is zero outside `U`. The actual conservative family of
algebraically closed points therefore shows that `j_!` preserves finite
limits. Its left adjunction proves preservation of finite colimits.
It follows that `j_!` is additive and preserves short exact sequences
of sheaves over any coefficient ring. Open immersions satisfy the stated
monomorphic étale hypothesis.

This is an exact functor on ordinary module sheaves. The relative
derived direct image obtained from it is described below; the
fiberwise compact-cohomology and trace comparisons remain separate.

## The fixed phase family

The coordinate ring

```text
B = F_p[t,u,u⁻¹,v,v⁻¹]
```

is constructed as an iterated Laurent polynomial ring. It has the single
function `u+v+t u⁻¹v⁻¹`, a projection to the affine parameter line, and the
character sheaf of that function. These objects are independent of the
field extension and of any point.

The Laurent universal property gives an equivalence between ring maps
`B→K` and triples `(t,u,v)` with `t∈K` and `u,v∈Kˣ`. This is transferred to
actual scheme points, and the actual points over `t` correspond exactly to
`Kˣ×Kˣ`. For finite `K`, the preceding trace theorem gives

```text
|K|⁻¹ ∑_{u,v∈Kˣ} tr(Frob_geom | stalk at (t,u,v))
  = |K|⁻¹ ∑_{u,v∈Kˣ} ψ(Tr(u+v+t/(uv)))
  = kl3(ψ∘Tr,t).
```

This is proved with the standard complex character and the existing
normalization of the finite sum, and specializes to the original prime-field
`kl3`. All parameter values, including zero, are included. The statement
identifies the integrand sheaf and its point traces. The normalization is
a scalar in this identity; it has not been realized as a Tate twist of
a direct-image sheaf.

## A proper model of the fixed family

Write `A=F_p[t]`. The projective plane over `A` is constructed using the
standard grading of `A[X,Y,Z]`, and its projection to `Spec A` is proved
proper. The degree-zero localization at `XYZ` is identified with
`A[u,u⁻¹,v,v⁻¹]`. The coordinates are `u=X/Z` and `v=Y/Z`; their inverses
are explicit homogeneous fractions. The ring equivalence is proved over
every commutative base ring, without a domain assumption.

Applying `Spec` gives an open immersion of the original phase scheme
into this projective plane. Its image is exactly `D₊(XYZ)` and is dense
when `p` is prime. Composing it with the proper projection gives exactly
the original projection to the parameter line. On the chart,

```text
(X²Y+XY²+tZ³)/(XYZ) = u+v+t/(uv).
```

This identity is proved for the existing phase function. The same open
immersion defines the actual extension-by-zero functor, including its
adjunction, exactness, and inside and outside geometric stalk formulas.
The properness here is relative to `Spec F_p[t]`. Global cohomology of
the total projective family alone would not identify the compactly
supported cohomology of the individual fibers.

## The actual relative derived direct image

For any scheme morphism `q:X→S`, the actual base-change functor sends an
étale `U→S` to `U×_S X→X`. It preserves finite limits and jointly
surjective étale covers. Thus precomposition gives the actual direct
image on module sheaves, with

```text
(q_*F)(U) = F(U×_S X).
```

This functor is proved additive and left exact. The category of module
sheaves on the small étale site is Grothendieck abelian, using the actual
essentially small affine étale subsite. It therefore has enough injectives.
The construction uses the resulting injective resolutions, applies the
same direct-image functor to them, and takes homology to define `R^n q_*`.
The degree-zero comparison with `q_*` is the canonical isomorphism.

For the unchanged compactified family, this gives the actual functor

```text
F ↦ R^n barπ_*(j!F)
```

with values in module sheaves on the original parameter line. This
construction works at every finite coefficient level. Proper base
change, identification of geometric stalks with compactly supported
cohomology of the fibers, adic coefficient/cohomology comparisons, and
Frobenius trace formulas remain to be proved.

## Inverse image and the canonical derived comparison

The actual direct-image functor preserves small limits and admits a left
adjoint on the existing small-étale module-sheaf categories. For a
geometric point `s` of `X`, the pullback universal property identifies
the stalk of `q*F` at `s` with the stalk of `F` at `s≫q`. The proved
conservative family of geometric points then proves finite-limit
preservation. The adjunction supplies finite-colimit preservation, so
this actual inverse image is exact for any coefficient ring.

The actual direct-image composition isomorphisms and the inverse-image
adjunctions define the ordinary unit-square-counit base-change map.
For an exact functor `G`, the image of an injective resolution is an
exact augmented complex. Its comparison to the chosen injective
resolution of the image object is constructed without requiring its
terms to be injective. Uniqueness up to homotopy proves naturality.
Applying the ordinary map degree by degree and then this comparison
constructs the derived base-change morphism. In degree zero, the
augmentation and cycle calculations identify it with the original
ordinary mate through the canonical `R^0q_* ≅ q_*` isomorphisms.

If `G` also preserves injectives and the original ordinary map is an
isomorphism, that same derived map is an isomorphism. These are explicit
hypotheses of the algebraic criterion. Actual direct image preserves
injectives because its left adjoint is exact. Restriction to an open
subscheme preserves injectives because extension by zero is exact; the
site adjunction identifies this restriction with the actual inverse
image, with compatible units and counits. No injectivity-preservation
claim is made for arbitrary inverse image.

For a literal Cartesian square whose base-changing morphism is an
étale monomorphism, the required neighborhood pullback factors through
the pulled-back open subscheme. This makes the unit factor of the
original ordinary mate invertible; its other factors are the proved
direct-image square isomorphism and the open-restriction counit.
Thus the original ordinary map is an isomorphism. The pulled-back
inverse image preserves injectives, so the same derived map is an
isomorphism in every nonnegative degree. The result includes the
unchanged compactification and its original extension by zero. It does
not prove proper base change along an arbitrary geometric point.

The actual derived functors are additive: the chosen resolution
descents respect addition up to the proved comparison homotopy.
Applying `R^d barπ_*j!` to the existing finite-level tower in the fixed
`Λ`-module category gives an actual inverse system in every degree.
Its level `n` remains annihilated by `ell^(n+1)` on every section.
This construction does not identify it with cohomology computed in a
different coefficient category or with adic cohomology.

## Actual cohomology on the geometric fiber

The open-base-change isomorphism also compares the right adjoints of
`j!` followed by inverse image and inverse image followed by the
pulled-back `j'!`. Conjugation gives an isomorphism between these actual
left adjoints for an arbitrary change of base. Applying the existing
derived direct image gives the original compact-support comparison with
the actual pulled-back extension in its target.

Global sections on a small étale site are evaluation at the identity
étale object, whose terminal property is proved. This agrees naturally
with the right adjoint of the constant-sheaf functor. Over a separably
closed field, the identity pointed neighborhood is initial in the
actual neighborhood category; its original germ map identifies these
global sections with the identity geometric stalk. Global sections are
therefore exact on that site.

Exact postcomposition of the existing injective-resolution derived
functors gives
`Γ(Spec Ω, R^n q_* F) ≅ H^n(X,F)` for `q:X→Spec Ω` and separably closed
`Ω`. Its degree-zero square retains the original resolution
augmentations. Together with the original inverse-image stalk
isomorphism, it transports the existing geometric-point base-change map
to a map from `(R^n q_*F)_s` to
`H^n(X×_S Spec Ω, (fst)^*F)`. The map is constructed; its invertibility
for proper `q` remains unproved.

For the original Kloosterman compactification, the proper model is
pulled back to the specified field. The pulled-back phase open is
identified with the literal fiber of the original phase projection by
pullback symmetry, pasting, and the proved original factorization.
Both projection identities are proved. The target cohomology is thus
global cohomology on this actual proper fiber of the original phase
sheaf, pulled back and extended by zero. It is not global cohomology of
the total family over the parameter line.

The original finite phase system in the fixed `Λ`-module category gives
a fiber-cohomology tower. Each level is annihilated by `ell^(n+1)`.
The same geometric comparison forms a natural transformation from the
relative derived-image stalk tower to this fiber tower, commuting with
the original coefficient reductions. The actual cone from the
limit-coefficient phase sheaf maps to a cohomology cone; no limit
property or adic comparison is asserted.

In degree zero the full transported geometric comparison agrees with
the original ordinary mate through the canonical zero isomorphisms on
both its source and actual fiber-cohomology target. This is a statement
about the same maps, without an invertibility conclusion.

The geometric lifting foundation now includes unique lifting of every
specified residue-field point of an arbitrary étale algebra over a
Henselian local ring. An actual localization at that point gives a
standard étale presentation. Existence then uses the monic simple-root
form of Hensel's lemma and the actual standard étale universal map.
Uniqueness holds already over a local ring. The constructed equivalence
has actual residue reduction as its forward map; neither a presentation
nor a lift is supplied as a hypothesis.
The same lifting theorem now holds for arbitrary étale schemes, using an
actual affine chart at the residue point. Over a strictly henselian local
ring it makes the identity neighborhood initial in the actual pointed
étale-neighborhood category. The resulting stalk comparison proves
exactness of the original global-sections functor and vanishing of its
positive cohomology. For any scheme over this base the actual closed-point
stalk of its relative derived image is the cohomology of the whole source,
with the original degree-zero maps retained.

For a universally closed map to a local base, an open containing the
actual closed fiber is the whole source. This applies to every proper
map. The open diagonal of an étale morphism then proves uniqueness for
maps, and in particular sections, agreeing on that closed fiber.
The original closed-fiber restriction of global sections of every module
sheaf is injective as well. Equality after restriction gives equality of
the actual closed-fiber germs; actual pointed étale neighborhoods and
the open-image detection lemma produce a covering, and separatedness
then proves equality of the original sections. A finite étale map to a
proper scheme over this local base is an isomorphism exactly when its
actual closed-fiber base change is an isomorphism.
Existence of extensions from the fiber is still required; no comparison
with its cohomology follows from uniqueness alone.

Across a henselian pair, the actual idempotent-reduction map is
bijective, and inverse image gives the corresponding clopen-subset
order isomorphism. For a henselian local base, the original universal
coprime-factorization algebra is étale, so the proved residue-point
equivalence gives unique lifting of coprime monic factorizations with
specified ordered degrees. Both coefficient reductions are retained.
For a finite commutative algebra `A` over the henselian local base `R`,
finite-module Cayley–Hamilton produces an annihilator `F` of `a(a-1)`
reducing to `X^N`, with `N>0`, whenever `a` represents a residue idempotent.
The preceding factorization theorem lifts the coprime residue factors
`X^N` and `(X-1)^N` of `F(X(X-1))`. Evaluating the lifted factors at `a`
gives a coprime zero product. Its actual Bézout identity constructs an
idempotent with exactly the prescribed residue. Integral contraction of
maximal ideals puts `mA` in the Jacobson radical and proves uniqueness.

In an arbitrary integral algebra, a finite coefficient witness for
`a(a-1) ∈ mA` descends this relation to a finite subalgebra containing `a`
and all those coefficients. The finite result and the actual inclusion
then give the lift in `A`. Thus the original idempotent reduction
`A → A/mA` is bijective for every integral algebra, and its actual
prime-spectrum pullback is an order isomorphism on clopen subsets.
The inverse agrees with the unique lifted idempotent. This requires no
finiteness, nontriviality, freeness, localness or henselianity of `A`.
The full simple-root property for `A`, and clopen lifting on proper
nonaffine schemes, are not asserted by this argument.

For any scheme, global idempotents classify its actual clopens. For a
proper map `X → Spec R`, the original factorization through
`Spec Γ(X)` has integral second factor and proper, surjective first
factor. Its original structure-sheaf map is an isomorphism; the latter
statement follows from basic-open localization for every qcqs scheme.
Nilpotent quotient base changes are actual homeomorphisms and preserve
global idempotents through the original section restriction map.
For an arbitrary ideal, every idempotent on the closed subscheme has a
unique compatible family on the actual infinitesimal neighborhoods
`X_n = X × Spec(R/I^(n+1))`; all original transition maps are retained.
Separately, a linear map out of an adic completion has the same range
on the original module if a power of its finitely generated ideal
annihilates the target. The remaining proper-fiber image theorem and
formal-functions comparison are described, with primary references, in
[`proper_affinization_gap.md`](proper_affinization_gap.md). None of these
statements asserts connectedness of the affinization fibers.

The original section restrictions now construct the canonical map from
completed global sections to compatible sections of these infinitesimal
schemes. Its coordinates and agreement with original global sections
are proved. For an affine scheme, the restriction is surjective with
the expected ideal-power kernel, so the same completion map is a linear
equivalence. Its inverse supplies a completed preimage of the original
idempotent family, without a finite-generation or Noetherian hypothesis.
Surjectivity for general proper schemes remains unproved. Separately,
global idempotents and clopens on a given cofiltered limit of qcqs
schemes with affine transitions descend to a stage, and equal
representatives agree at a common later stage. This proves descent from
a given diagram; constructing proper Noetherian models remains separate.

The existing right derived functors are naturally identified with
cohomology of the bounded-below derived functor applied to objects
concentrated in degree zero. This comparison uses the same injective
resolutions and intertwines the original degree-zero augmentation with
the actual derived-functor unit. The bounded-below derived functor is
proved triangulated. The actual short-exact-sequence triangles and their
natural maps yield the long exact sequence for the original ordinary
right derived functors. Dimension shifting on the actual cycle sequences
and the degree-zero connecting cokernels prove that an acyclic resolution
computes those same functors through the original comparison map.

Consequently the existing derived base-change map is an isomorphism if
its original ordinary mate is invertible and the exact source functor
sends injectives to objects acyclic for the target functor. The proof
uses a quasi-isomorphism of the original comparison complex, without a
homotopy-equivalence assumption. The original degree-zero square is
preserved. These geometric premises remain unproved for the proper map.

For the original limit and finite coefficient rings, powers of `ell`
are regular on the limit and the kernels of the original reductions
are their stated power ideals. The projected identity sections compare
the actual character coefficient maps with the literal scalar maps on
geometric stalks. This proves the original coefficient short exact
sequence. The original exact `j!` and derived projection give its
Bockstein long exact sequence, including the derived objects computed
in their actual finite coefficient categories. Its connecting maps
respect the original sequence transitions, with the complementary
power `ell^(n-m)` in the next degree. These are ordinary sheaf
cohomology statements. The original scalar, reduction, and connecting
maps assemble into exact triples in the category of inverse systems,
with complementary-power transitions in the next-degree terms. No
inverse limit is taken; the adic comparison remains unproved. The maps
and exact scope are explained in
[`coefficient_bockstein_scope.md`](coefficient_bockstein_scope.md).

The coefficient-category comparison can be completed independently of
proper base change. The original skyscraper at an actual point is exact:
on every étale object it is a product of copies of the original module.
Small products of skyscrapers are exact by nested module products, and
the original stalk-family adjunction shows that they preserve injective
objects. Their global sections are the original product of coefficients,
so all positive global cohomology vanishes. Direct image of an actual
geometric skyscraper is the skyscraper at the composed point, through
the original inverse-image stalk isomorphism and adjunctions. The same
product comparison proves vanishing of positive relative derived direct
images of these products for every scheme morphism.

The product of the original stalk-adjunction units at the canonical
algebraic-closure points is a monomorphism: the original counits split
its stalk maps, and the proved conservative family detects monicity.
Every injective sheaf is therefore an actual retract of that product.
Coefficient restriction is exact and commutes with these skyscrapers
and products through their original projections. The mapped retract
proves acyclicity of restricted injectives for both global sections and
relative direct image. Consequently the original derived coefficient
comparisons are isomorphisms for every ring map, with their literal
ordinary squares and original degree-zero augmentations. No flatness
or preservation of injectives by coefficient restriction is assumed.
The original module restriction also has its actual coextension as a
right adjoint on sheaves. Coextension commutes literally with restriction
to an étale object. Taking the mate through these original adjunctions
proves that coefficient restriction commutes with the original extension
by zero. Combining this with the relative derived comparison gives the
same comparison for `R^n barπ_*(j!F)`. Its forward component is the
original derived coefficient map followed by the derived image of the
original extension comparison. The full degree-zero augmentation square
is retained.

At every finite torsion level, applying this to the original phase sheaf
identifies the actual derived image in its finite coefficient category,
after restriction along `Λ → Λ_n`, with the corresponding object of the
existing common-coefficient tower. This is a levelwise comparison;
the original derived maps also satisfy composition and transformation
laws, proved using the original resolution homotopies and canonical
homology comparisons. The original extension comparison satisfies the
same coefficient-composition law through its original adjunction unit.

The transition in the level-n coefficient category is defined as
`D_n(reduction_nm)` followed by the inverse original coefficient
comparison at level m. Restricting it along `Λ → Λ_n` and the original
projection-composition isomorphism gives a map in the common category.
The existing levelwise comparisons intertwine this independently
defined map with `D_Λ` of the original common-coefficient reduction.
Thus the actual finite-category derived objects, with these maps, form
an inverse system naturally isomorphic to the original tower.
Composition also holds within the finite coefficient categories, before
restriction to the common ring, with the original scalar-composition
isomorphism. Its proof uses the original finite sheaf reductions and
the coefficient-comparison composition law.
Cohomology through the inverse limit and adic cohomology remain open.

## Entry points and limits

- `formal/TypeIIIArtinSchreierCover.lean` and
  `formal/TypeIIIArtinSchreierScheme.lean`: actual finite étale cover.
- `formal/TypeIIIArtinSchreierSchemeTorsor.lean`: actual torsor isomorphism.
- `formal/TypeIIIArtinSchreierRingSheaf.lean` and
  `formal/TypeIIIArtinSchreierRingStalk.lean`: actual image-stalk
  comparison and freeness of rank one over commutative coefficient rings.
- `formal/TypeIIIArtinSchreierRingTrace.lean`: actual geometric Frobenius
  trace over those rings. `formal/TypeIIIArtinSchreierPointTrace.lean`
  includes the field and complex prime-field specializations.
- `formal/TypeIIIArtinSchreierPointFiber.lean`: original cover fibers at
  field-valued points of an arbitrary affine base.
- `formal/TypeIIIArtinSchreierRingGenerator.lean` and
  `formal/TypeIIIArtinSchreierRingLocalTriviality.lean`: the actual
  generating section and local trivialization on the cover.
- `formal/TypeIIITorsionCoefficients.lean`,
  `formal/TypeIIITorsionCoefficientLimit.lean`, and
  `formal/TypeIIIArtinSchreierTorsionSheaf.lean`: finite cyclotomic
  coefficient rings, their topological inverse limit, and the actual
  locally trivial sheaves and Frobenius traces at finite levels.
- `formal/TypeIIITorsionCoefficientCoordinates.lean`,
  `formal/TypeIIITorsionCoefficientQuotient.lean`,
  `formal/TypeIIITorsionCoefficientLimitTopology.lean`, and
  `formal/TypeIIITorsionCoefficientComplete.lean`: the actual finite free
  `Z_ell`-coordinates, finite quotient identifications, adic topology,
  Noetherian property, and adic completeness of the original ring.
- `formal/TypeIIIArtinSchreierLimitSheaf.lean`: the actual limit-coefficient
  sheaf, its canonical tensor comparisons to finite levels, the inverse
  system of limit-ring module sheaves, and the compatible cone.
- `formal/TypeIIIArtinSchreierCoefficientMaps.lean` and
  `formal/TypeIIIArtinSchreierTorsionTower.lean`: actual coefficient
  transitions, their image-inclusion and composition laws, and the
  resulting inverse system of additive sheaves.
- `formal/TypeIIISplitImageTransport.lean`,
  `formal/TypeIIIArtinSchreierCoefficientExtension.lean`, and
  `formal/TypeIIIArtinSchreierTorsionBaseChange.lean`: the actual
  extension-of-scalars isomorphisms and identification of their adjoints
  with the original coefficient maps, including every finite reduction.
- `formal/TypeIIISliceLeftKan.lean`,
  `formal/TypeIIIEtaleExtensionByZero.lean`, and
  `formal/TypeIIIEtaleExtensionExact.lean`: actual extension by zero,
  its adjunction and geometric stalk formulas, and its exactness.
- `formal/TypeIIIKloostermanPhaseFamily.lean` and
  `formal/TypeIIIKloostermanPhasePoints.lean`: the fixed affine phase family,
  its complete point parametrization, and the normalized trace-sum identity.
- `formal/TypeIIIProjectivePlaneModel.lean`,
  `formal/TypeIIIHomogeneousEvaluation.lean`,
  `formal/TypeIIIProjectiveTorusChart.lean`, and
  `formal/TypeIIIKloostermanCompactification.lean`: the actual proper
  projective model, torus-chart equivalence, unchanged projection and
  phase identities, and extension by zero for the original family.
- `formal/TypeIIIEtaleDirectImage.lean` and
  `formal/TypeIIIEtaleDerivedDirectImage.lean`: actual small-étale direct
  image, its injective-resolution construction, and the relative derived
  direct image for the fixed compactification.
- `formal/TypeIIIEtaleInverseImage.lean` and
  `formal/TypeIIIEtaleInverseImageStalk.lean`: actual inverse image,
  its adjunction, geometric-stalk comparison, and exactness.
- `formal/TypeIIIEtaleDirectImageComposition.lean` and
  `formal/TypeIIIEtaleInverseImageComposition.lean`: the actual
  composition isomorphisms and ordinary base-change mate.
- `formal/TypeIIIExactResolutionComparison.lean`,
  `formal/TypeIIIExactFunctorResolution.lean`,
  `formal/TypeIIIDerivedBaseChange.lean`, and
  `formal/TypeIIIEtaleDerivedBaseChange.lean`: exact-source comparison,
  its homotopy naturality, and the actual derived base-change morphism.
- `formal/TypeIIIDerivedBaseChangeZero.lean` and
  `formal/TypeIIIEtaleDerivedBaseChangeZero.lean`: the same derived
  morphism agrees in degree zero with the original ordinary mate.
- `formal/TypeIIIExactFunctorInjectiveResolution.lean`,
  `formal/TypeIIIDerivedBaseChangeIso.lean`,
  `formal/TypeIIIEtaleInjectiveImages.lean`, and
  `formal/TypeIIIEtaleRestrictionInverseImage.lean`: the isomorphism
  criterion and the proved injective-preservation results for actual
  direct image and restriction to an open subscheme.
- `formal/TypeIIIEtaleOpenBaseChange.lean` and
  `formal/TypeIIIEtaleDerivedOpenBaseChange.lean`: the original ordinary
  and derived Cartesian base-change maps are isomorphisms for étale
  monomorphisms, including the fixed compactification specialization.
- `formal/TypeIIIInjectiveResolutionAdditivity.lean` and
  `formal/TypeIIIKloostermanTorsionDerivedTower.lean`: additivity of the
  actual derived functors and the fixed-coefficient derived tower with
  its original torsion exponents.
- `formal/TypeIIIEtaleOpenExtensionBaseChange.lean` and
  `formal/TypeIIIEtaleCompactSupportBaseChange.lean`: arbitrary pullback
  of the actual extension by zero and the original derived comparison
  with the actual pulled-back open extension as target.
- `formal/TypeIIIEtaleCohomology.lean`,
  `formal/TypeIIIEtaleClosedFieldSections.lean`,
  `formal/TypeIIIRightDerivedPostcompose.lean`, and
  `formal/TypeIIIEtaleGeometricFiberCohomology.lean`: actual global
  sections, exactness over a separably closed field, and the target of
  the original geometric-point map as cohomology of the literal fiber.
- `formal/TypeIIIKloostermanFiberCompactification.lean`,
  `formal/TypeIIIKloostermanFiberBaseChange.lean`, and
  `formal/TypeIIIKloostermanTorsionFiberTower.lean`: the original phase
  open on the actual proper fiber, its cohomology, the unchanged
  base-change comparison, and the original finite coefficient system.
- `formal/TypeIIIEtaleGeometricFiberCohomologyZero.lean`: the full
  geometric comparison in degree zero agrees with the original ordinary
  mate through both canonical zero isomorphisms.
- `formal/TypeIIIHenselianEtaleSections.lean` and
  `formal/TypeIIIHenselianEtaleLifting.lean`: actual unique lifting of
  specified residue-field points of arbitrary étale algebras.
- `formal/TypeIIIRightDerivedPlusComparison.lean`: natural comparison
  with bounded-below derived-category cohomology, including the actual
  unit identity in degree zero.
- `formal/TypeIIIHenselianEtaleScheme.lean`,
  `formal/TypeIIIStrictHenselianEtaleSections.lean`, and
  `formal/TypeIIIStrictHenselianEtaleCohomology.lean`: unique étale section
  lifting, exact global sections over a strictly henselian local base,
  and the cohomology of the actual whole source over that base.
- `formal/TypeIIIProperLocalClosedFiber.lean`: detection by the actual
  closed fiber and uniqueness of étale section extensions.
- `formal/TypeIIIRightDerivedPlusTriangulated.lean`,
  `formal/TypeIIIDerivedPlusSingleTriangle.lean`, and
  `formal/TypeIIIRightDerivedLongExact.lean`: triangulatedness and natural
  long exact sequences for the original derived functors.
- `formal/TypeIIIExactResolutionCycles.lean`,
  `formal/TypeIIIExactResolutionQuasiIso.lean`,
  `formal/TypeIIILeftExactCochainHomology.lean`,
  `formal/TypeIIIAcyclicResolutionComparison.lean`, and
  `formal/TypeIIIDerivedBaseChangeAcyclic.lean`: actual cycle sequences and
  mapped homology, the acyclic-resolution comparison, and invertibility
  of the same derived map under the explicit acyclicity hypothesis.
- `formal/TypeIIIEtaleDerivedAcyclicBaseChange.lean`: the criterion for
  the actual étale pullback map, retaining its geometric premises.
- `formal/TypeIIIEtaleSectionsRestriction.lean` and
  `formal/TypeIIIProperLocalSectionsInjective.lean`: the actual
  closed-fiber section map and its injectivity for module sheaves.
- `formal/TypeIIIProperFiniteEtaleDetection.lean`: detection of actual
  finite étale isomorphisms on the closed fiber of a proper local scheme.
- `formal/TypeIIIHenselianIdempotentLifting.lean` and
  `formal/TypeIIIHenselianFactorizationLifting.lean`: actual idempotent
  and coprime monic-factorization reductions and their lifting bijections.
- `formal/TypeIIICoprimeIdempotentLifting.lean`,
  `formal/TypeIIIFiniteAlgebraAnnihilator.lean`,
  `formal/TypeIIIFiniteAlgebraJacobson.lean`, and
  `formal/TypeIIIFiniteAlgebraIdempotentLifting.lean`: finite-module
  annihilators, actual coprime factors and Bézout idempotents, with
  uniqueness from the actual Jacobson radical.
- `formal/TypeIIIIntegralAlgebraFiniteDescent.lean` and
  `formal/TypeIIIIntegralAlgebraIdempotentLifting.lean`: descent of the
  finite relation witness and unique idempotent lifting for every
  integral algebra over the henselian local base.
- `formal/TypeIIIFiniteAlgebraClopenLifting.lean` and
  `formal/TypeIIIIntegralAlgebraClopenLifting.lean`: the original
  quotient-spectrum pullback as an order isomorphism on clopens,
  including the actual inverse-idempotent formulas.
- `formal/TypeIIIEtaleSkyscraperExact.lean`,
  `formal/TypeIIIEtaleSkyscraperCohomology.lean`,
  `formal/TypeIIIEtaleSkyscraperFamily.lean`, and
  `formal/TypeIIIEtaleSkyscraperFamilyCohomology.lean`: actual skyscrapers,
  their products, exactness, adjunctions, and global-cohomology vanishing.
- `formal/TypeIIIEtaleSkyscraperDirectImage.lean` and
  `formal/TypeIIIEtaleSkyscraperFamilyDirectImage.lean`: the original
  direct-image comparisons and relative acyclicity of those products.
- `formal/TypeIIIEtaleGodementRetract.lean`: the actual canonical
  embedding and its retraction for injective sheaves.
- `formal/TypeIIIEtaleCoefficientRestriction.lean`,
  `formal/TypeIIIEtaleCoefficientSkyscraperFamily.lean`,
  `formal/TypeIIIEtaleCoefficientCohomology.lean`, and
  `formal/TypeIIIEtaleCoefficientDerivedDirectImage.lean`: exact
  coefficient restriction, original product projections, and the same
  global and relative derived comparison isomorphisms.
- `formal/TypeIIIEtaleCoefficientCoextension.lean` and
  `formal/TypeIIIEtaleExtensionCoefficientRestriction.lean`: the
  original coefficient coextension adjunction and its actual mate
  giving the extension-by-zero comparison.
- `formal/TypeIIIEtaleCompactSupportCoefficientRestriction.lean` and
  `formal/TypeIIIKloostermanTorsionCoefficientComparison.lean`: the
  original compactified derived-image comparison and the levelwise
  identification with actual finite-coefficient derived images.
- `formal/TypeIIIDerivedBaseChangeComposition.lean` and
  `formal/TypeIIIDerivedBaseChangeTransformation.lean`: pasting and
  transformation laws for the original derived comparisons, from the
  original resolution and homology maps.
- `formal/TypeIIIEtaleDerivedCoefficientComposition.lean` and
  `formal/TypeIIIEtaleCompactSupportCoefficientComposition.lean`:
  composition of the original coefficient comparisons.
- `formal/TypeIIIKloostermanFiniteCoefficientTransitions.lean`: the
  independently defined finite-category transitions and the actual
  isomorphism of inverse systems with the original tower.
- `formal/TypeIIIKloostermanFiniteCoefficientComposition.lean`:
  composition of those transitions within the finite coefficient
  categories, with the original scalar-composition isomorphism.
- `formal/TypeIIIProperAffinization.lean` and
  `formal/TypeIIIProperAffinizationStructureSheaf.lean`: the actual
  proper factorization and original structure-sheaf isomorphism.
- `formal/TypeIIINilpotentThickeningIdempotents.lean` and
  `formal/TypeIIIAdicCompletionRangeDescent.lean`: original global
  idempotent restriction and the algebraic completed-map range theorem.
- `formal/TypeIIIInfinitesimalIdempotentTower.lean`: the original
  infinitesimal schemes, quotient-induced transitions, and unique
  compatible family of idempotents, without a lift-to-global-sections claim.
- `formal/TypeIIIInfinitesimalSections.lean`,
  `formal/TypeIIIAdicCompatibleSystem.lean`, and
  `formal/TypeIIIInfinitesimalCompletion.lean`: original section
  modules, restrictions, and the canonical completed comparison, with
  its normalization and completed-to-original range descent.
- `formal/TypeIIIInfinitesimalAffineSections.lean`,
  `formal/TypeIIIAdicCompatibleSystemEquivalence.lean`, and
  `formal/TypeIIIInfinitesimalAffineCompletion.lean`: the exact affine
  restriction kernel and bijectivity of the original completion map.
- `formal/TypeIIIAffineLimitIdempotentDescent.lean`: original
  idempotent and clopen descent from a given scheme limit, and eventual
  equality of representatives.
- `formal/TypeIIITorsionCoefficientExactness.lean`,
  `formal/TypeIIIArtinSchreierCoefficientGenerator.lean`, and
  `formal/TypeIIIArtinSchreierBockstein.lean`: original scalar kernels,
  the coefficient-map generator square, and sheaf short exactness.
- `formal/TypeIIIArtinSchreierBocksteinTransitions.lean`,
  `formal/TypeIIIKloostermanBockstein.lean`,
  `formal/TypeIIIKloostermanBocksteinTransitions.lean`, and
  `formal/TypeIIIKloostermanFiniteBockstein.lean`: original
  coefficient-sequence transitions and natural long exact sequences,
  including the finite-category derived objects.
- `formal/TypeIIIKloostermanBocksteinSystem.lean`: the original
  finite connecting-map naturality and all three exact triples in
  the category of sheaf-valued inverse systems.

These are ordinary module-valued sheaves, including the stated finite
torsion coefficients. The constructions do not yet provide the required
adic cohomology comparisons, invertibility of the constructed proper
stalk-to-fiber-cohomology map, the trace formula, the normalized
rank-three Kloosterman sheaf, purity, or the uniform geometric estimates
needed by Type III. A discrete complex or `Λ`-module sheaf does not supply
the missing adic cohomology comparisons by itself.
The precise remaining target and its quantifiers are unchanged in
`formal/TypeIIILocal.lean`.

The current repository-wide verification receipt and reproduction command
are recorded in `STATUS.md` and `docs/verification.md`.
