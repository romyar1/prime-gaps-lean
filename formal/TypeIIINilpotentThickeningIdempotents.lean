import TypeIIISchemeIdempotentClopens
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Global idempotents on actual nilpotent thickenings

For an ideal I of a commutative ring R with I^N = 0, and any actual
morphism q : X → Spec R, the pullback of Spec(R/I) → Spec R has the
same underlying topological space as X.  Nilpotence proves surjectivity
of the quotient spectrum map; actual base-change stability of closed
immersions and surjectivity gives the homeomorphism after pullback.

The existing classification of global idempotents by clopens, including
its naturality for the original maps on sections, then proves that the
original restriction on global idempotents is bijective.  No properness,
Noetherianity, quasi-compactness, nonemptiness, or given lift is assumed.
This is nilpotent-thickening invariance, not a formal-functions theorem.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.NilpotentThickeningIdempotents

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Topology
open scoped AlgebraicGeometry

/-- The actual idempotents of the original ring of global sections. -/
abbrev GlobalIdempotents (X : Scheme.{u}) := {e : Γ(X, ⊤) // IsIdempotentElem e}

/-- Restriction is the original map on global sections, restricted to idempotents. -/
def idempotentRestriction {X Y : Scheme.{u}} (j : X ⟶ Y)
    (e : GlobalIdempotents Y) : GlobalIdempotents X :=
  ⟨j.appTop e.1, e.2.map j.appTop.hom⟩

/-- The restriction has the original, literal value on global sections. -/
theorem idempotentRestriction_apply {X Y : Scheme.{u}} (j : X ⟶ Y)
    (e : GlobalIdempotents Y) : (idempotentRestriction j e).1 = j.appTop e.1 := rfl

/-- Restricting twice is restriction along the original composite morphism. -/
theorem idempotentRestriction_comp {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    (e : GlobalIdempotents Z) :
    idempotentRestriction (i ≫ j) e = idempotentRestriction i (idempotentRestriction j e) := by
  apply Subtype.ext
  change (i ≫ j).appTop e.1 = i.appTop (j.appTop e.1)
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- An actual scheme homeomorphism induces a bijection by literal clopen inverse image. -/
theorem clopenPullback_bijective_of_isHomeomorph {X Y : Scheme.{u}} (j : X ⟶ Y)
    (hj : IsHomeomorph j) : Function.Bijective (SchemeIdempotentClopens.clopenPullback j) := by
  let e := hj.homeomorph j
  constructor
  · intro U V h
    apply Clopens.ext
    ext y
    obtain ⟨x, rfl⟩ := hj.surjective y
    exact SetLike.ext_iff.mp h x
  · intro U
    refine ⟨⟨e.symm ⁻¹' (U : Set X), U.isClopen.preimage e.symm.continuous⟩, ?_⟩
    apply Clopens.ext
    ext x
    change e.symm (e x) ∈ U ↔ x ∈ U
    rw [e.symm_apply_apply]

/-- The proved global-idempotent classification transports the actual restriction map. -/
theorem idempotentRestriction_bijective_of_isHomeomorph {X Y : Scheme.{u}} (j : X ⟶ Y)
    (hj : IsHomeomorph j) : Function.Bijective (idempotentRestriction j) := by
  have hc := clopenPullback_bijective_of_isHomeomorph j hj
  constructor
  · intro e f h
    apply (SchemeIdempotentClopens.globalIdempotentClopenEquiv Y).injective
    apply hc.injective
    rw [← SchemeIdempotentClopens.globalIdempotentClopenEquiv_naturality,
      ← SchemeIdempotentClopens.globalIdempotentClopenEquiv_naturality]
    exact congrArg (SchemeIdempotentClopens.globalIdempotentClopenEquiv X) h
  · intro e
    obtain ⟨U, hU⟩ := hc.surjective (SchemeIdempotentClopens.globalIdempotentClopenEquiv X e)
    refine ⟨(SchemeIdempotentClopens.globalIdempotentClopenEquiv Y).symm U, ?_⟩
    apply (SchemeIdempotentClopens.globalIdempotentClopenEquiv X).injective
    rw [show SchemeIdempotentClopens.globalIdempotentClopenEquiv X
        (idempotentRestriction j ((SchemeIdempotentClopens.globalIdempotentClopenEquiv Y).symm U)) =
          SchemeIdempotentClopens.clopenPullback j
            (SchemeIdempotentClopens.globalIdempotentClopenEquiv Y
              ((SchemeIdempotentClopens.globalIdempotentClopenEquiv Y).symm U)) from
      SchemeIdempotentClopens.globalIdempotentClopenEquiv_naturality j _,
      OrderIso.apply_symm_apply]
    exact hU

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The original quotient spectrum morphism. -/
def quotientSpec : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- Every original quotient spectrum morphism is a closed immersion. -/
instance quotientSpec_isClosedImmersion : IsClosedImmersion (quotientSpec I) := by
  unfold quotientSpec
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- A vanishing ideal power puts each element of the ideal in the actual nilradical. -/
theorem le_nilradical_of_pow_eq_bot {N : ℕ} (hI : I ^ N = ⊥) : I ≤ nilradical R := by
  intro x hx
  rw [mem_nilradical]
  exact ⟨N, Ideal.mem_bot.mp (hI ▸ Ideal.pow_mem_pow hx N)⟩

/-- Nilpotence proves surjectivity of the actual quotient spectrum morphism. -/
theorem quotientSpec_surjective_of_nilpotent {N : ℕ} (hI : I ^ N = ⊥) :
    Surjective (quotientSpec I) := by
  constructor
  exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (le_nilradical_of_pow_eq_bot I hI)).surjective

variable {X : Scheme.{u}} (q : X ⟶ Spec (.of R))

/-- The thickening is the literal scheme pullback over the original affine base. -/
abbrev thickening : Scheme.{u} := pullback q (quotientSpec I)

/-- Its original projection to X. -/
def inclusion : thickening I q ⟶ X := pullback.fst q (quotientSpec I)

/-- The original projection is a closed immersion by actual base-change stability. -/
instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion I q) := by
  unfold inclusion
  infer_instance

/-- Nilpotence proves surjectivity after arbitrary actual scheme base change. -/
theorem inclusion_surjective_of_nilpotent {N : ℕ} (hI : I ^ N = ⊥) :
    Surjective (inclusion I q) := by
  have := quotientSpec_surjective_of_nilpotent I hI
  unfold inclusion
  infer_instance

/-- The literal thickening inclusion is a homeomorphism on underlying spaces. -/
theorem inclusion_isHomeomorph_of_nilpotent {N : ℕ} (hI : I ^ N = ⊥) :
    IsHomeomorph (inclusion I q) := by
  have := inclusion_surjective_of_nilpotent I q hI
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(inclusion I q).isClosedEmbedding.isEmbedding, (inclusion I q).surjective⟩

/-- Restriction by the original nilpotent-thickening inclusion is bijective on global idempotents. -/
theorem idempotentRestriction_bijective_of_nilpotent {N : ℕ} (hI : I ^ N = ⊥) :
    Function.Bijective (idempotentRestriction (inclusion I q)) :=
  idempotentRestriction_bijective_of_isHomeomorph (inclusion I q)
    (inclusion_isHomeomorph_of_nilpotent I q hI)

/-- The equivalence packages the original restriction, with no chosen substitute map. -/
def idempotentRestrictionEquiv {N : ℕ} (hI : I ^ N = ⊥) :
    GlobalIdempotents X ≃ GlobalIdempotents (thickening I q) :=
  Equiv.ofBijective (idempotentRestriction (inclusion I q))
    (idempotentRestriction_bijective_of_nilpotent I q hI)

/-- The forward equivalence is the original restriction. -/
theorem idempotentRestrictionEquiv_apply {N : ℕ} (hI : I ^ N = ⊥) (e : GlobalIdempotents X) :
    idempotentRestrictionEquiv I q hI e = idempotentRestriction (inclusion I q) e := rfl

/-- Its inverse gives the unique actual global lift with the specified restriction. -/
theorem idempotentRestrictionEquiv_symm_spec {N : ℕ} (hI : I ^ N = ⊥)
    (e : GlobalIdempotents (thickening I q)) :
    (inclusion I q).appTop ((idempotentRestrictionEquiv I q hI).symm e).1 = e.1 :=
  congrArg Subtype.val ((idempotentRestrictionEquiv I q hI).apply_symm_apply e)

/-- Every idempotent section on the actual thickening has a unique idempotent lift on X. -/
theorem existsUnique_idempotent_lift {N : ℕ} (hI : I ^ N = ⊥)
    (e : Γ(thickening I q, ⊤)) (he : IsIdempotentElem e) :
    ∃! a : Γ(X, ⊤), IsIdempotentElem a ∧ (inclusion I q).appTop a = e := by
  obtain ⟨a, ha⟩ := (idempotentRestriction_bijective_of_nilpotent I q hI).surjective ⟨e, he⟩
  refine ⟨a.1, ⟨a.2, congrArg Subtype.val ha⟩, ?_⟩
  intro b hb
  have hba : idempotentRestriction (inclusion I q) ⟨b, hb.1⟩ =
      idempotentRestriction (inclusion I q) a :=
    (Subtype.ext hb.2).trans ha.symm
  exact congrArg Subtype.val ((idempotentRestriction_bijective_of_nilpotent I q hI).injective hba)

end PrimeGap182.TypeIII.NilpotentThickeningIdempotents

#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.GlobalIdempotents
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestriction
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestriction_apply
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestriction_comp
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.clopenPullback_bijective_of_isHomeomorph
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestriction_bijective_of_isHomeomorph
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.quotientSpec
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.quotientSpec_isClosedImmersion
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.le_nilradical_of_pow_eq_bot
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.quotientSpec_surjective_of_nilpotent
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.thickening
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.inclusion
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.inclusion_isClosedImmersion
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.inclusion_surjective_of_nilpotent
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.inclusion_isHomeomorph_of_nilpotent
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestriction_bijective_of_nilpotent
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestrictionEquiv
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestrictionEquiv_apply
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.idempotentRestrictionEquiv_symm_spec
#print axioms PrimeGap182.TypeIII.NilpotentThickeningIdempotents.existsUnique_idempotent_lift
