# The derived limit of the coefficient tower

Fix distinct primes `p` and `ell`, and write `Λ` for the constructed
coefficient limit and `Λ_n` for its quotient modulo `ell^(n+1)`. Let
`j : U → X` be the original Kloosterman phase open immersion into its
proper model, and let `q : X → S` be the original projection. The tower
used here is

\[
T_n=j_!\bigl(\operatorname{Res}_{\Lambda}^{\Lambda_n}L_n\bigr).
\]

Its maps are the original coefficient reductions followed by the same
extension functor. Thus the extension by zero is performed before the
tower is resolved. This order is recorded in
[`TypeIIIKloostermanExtendedTower.lean`](../../../formal/TypeIIIKloostermanExtendedTower.lean).
The same file compares this tower with the extensions computed in each
finite coefficient category, after restriction to `Λ`. The comparison
respects the independently defined finite-coefficient transitions.

For a scheme `Y`, let `C_Y` be its category of small-étale `Λ`-module
sheaves, and let `Tow(C_Y)` be the category of functors from `ℕᵒᵖ` to
`C_Y`. The ordinary inverse limit is the original categorical functor

\[
L_Y:\operatorname{Tow}(C_Y)\longrightarrow C_Y.
\]

The tower category is Grothendieck abelian and therefore has enough
injectives. These facts, the original limit projections, and the right
derived functors of `L_Y` are proved in
[`TypeIIISheafTowerDerivedLimit.lean`](../../../formal/TypeIIISheafTowerDerivedLimit.lean).
The proof uses the pinned Mathlib constructions of separators for
presheaf categories, pointwise exact filtered colimits, and injectives
in Grothendieck categories. No resolution-existence assumption is added.

Let `Q` apply the original `q_*` at every coefficient level. The original
adjunction `q^* ⊣ q_*` induces an adjunction on towers. Since `q^*` is
exact, `Q` preserves injectives. Likewise, the exact constant-tower
functor is left adjoint to `L_Y`, so `L_Y` preserves injectives. The
ordinary direct image commutes with the ordinary limit:

\[
q_*L_XT\ \cong\ L_SQT.
\]

This is the original limit-preservation map. Composing it with the
projection to level `n` gives `q_*` applied to the original projection
`L_XT → T_n`; see
[`TypeIIIEtaleTowerDirectImage.lean`](../../../formal/TypeIIIEtaleTowerDirectImage.lean).

The corresponding statement for full bounded below derived complexes is

\[
Rq_*\,RL_X(T)\ \cong\ RL_S\,RQ(T).
\]

It is proved in
[`TypeIIIEtaleDerivedLimitDirectImage.lean`](../../../formal/TypeIIIEtaleDerivedLimitDirectImage.lean).
The generic composition theorem in
[`TypeIIIRightDerivedPlusComposition.lean`](../../../formal/TypeIIIRightDerivedPlusComposition.lean)
uses the original derived-functor units. On a bounded below complex of
injectives, the first functor preserves the injective terms, so both
unit maps are isomorphisms. Mathlib's injective derivability structure
then supplies the universal property of the composite. The formal
normalization equation ties the resulting isomorphism to the ordinary
limit-preservation map above.

The notation `RQ(T)` denotes one derived object in the category of
towers. It retains the whole complex, as well as all coefficient
transitions. It does not denote a single tower `R^d q_*T_n`. The
construction therefore does not replace `H^d(RL_S RQ(T))` by the
ordinary limit of `R^d q_*T_n`. Such a replacement needs additional
theorems.

The existing Bockstein sequences, described in the
[coefficient exact-sequence note](coefficient_bockstein_scope.md), remain
sequences of ordinary sheaves and of towers. Their exactness does not
establish exactness of inverse limits. Nor does the present derived
interchange identify ordinary discrete `Λ`-sheaf cohomology with the
required adic theory. Cohomological finiteness, the necessary coefficient
and geometric base-change comparisons, and the trace formula remain to
be established before this construction supplies the Kloosterman sheaf
and the Type III Fourier estimate.
