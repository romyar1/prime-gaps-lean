import TypeIIINilpotentThickeningIdempotents
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Compatible global idempotents on the actual infinitesimal tower

For an arbitrary ideal I of R and q : X → Spec R, let X_n be the literal
pullback along Spec(R/I^(n+1)) → Spec R.  The transition X_m → X_n for
m ≤ n uses the original quotient-factor ring map.  Its first projection
to X is the original first projection of X_m.

All positive powers of I have the same vanishing locus.  Hence these
actual transitions are surjective closed immersions and homeomorphisms
on underlying spaces.  Restriction of global idempotents is therefore
bijective, and every prescribed idempotent on X_0 determines a unique
compatible family on the entire actual tower.

The ideal I need not be nilpotent.  There is no properness, Noetherianity,
quasi-compactness, nonemptiness, or formal-functions assumption.  No lift
from this family to a section of the original scheme X is asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.InfinitesimalIdempotentTower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Topology NilpotentThickeningIdempotents
open scoped AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The literal quotient spectrum map has image the actual vanishing locus. -/
theorem quotientSpec_range :
    Set.range (quotientSpec I) = PrimeSpectrum.zeroLocus (I : Set R) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- The actual spectrum morphism induced by reduction between positive ideal powers. -/
def quotientTransition {m n : ℕ} (hmn : m ≤ n) :
    Spec (.of (R ⧸ I ^ (m + 1))) ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn))))

/-- The quotient transition lies over the original Spec R. -/
theorem quotientTransition_comp_base {m n : ℕ} (hmn : m ≤ n) :
    quotientTransition I hmn ≫ quotientSpec (I ^ (n + 1)) = quotientSpec (I ^ (m + 1)) := by
  unfold quotientTransition quotientSpec
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext x
  rfl

variable {X : Scheme.{u}} (q : X ⟶ Spec (.of R))

/-- The n-th scheme is the original base change by R → R/I^(n+1). -/
abbrev thickening (n : ℕ) : Scheme.{u} :=
  NilpotentThickeningIdempotents.thickening (I ^ (n + 1)) q

/-- The original first projection from the n-th thickening to X. -/
def inclusion (n : ℕ) : thickening I q n ⟶ X :=
  NilpotentThickeningIdempotents.inclusion (I ^ (n + 1)) q

/-- Every original first projection is a closed immersion. -/
instance inclusion_isClosedImmersion (n : ℕ) : IsClosedImmersion (inclusion I q n) := by
  unfold inclusion
  infer_instance

/-- Every member of the tower has the same actual image in X. -/
theorem inclusion_range (n : ℕ) :
    Set.range (inclusion I q n) = q ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
  change Set.range (pullback.fst q (quotientSpec (I ^ (n + 1)))) = _
  rw [Scheme.Pullback.range_fst, quotientSpec_range,
    PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero n)]

/-- The actual transition induced by the quotient-factor map and the universal property
of the same literal scheme pullbacks. -/
def transition {m n : ℕ} (hmn : m ≤ n) : thickening I q m ⟶ thickening I q n :=
  pullback.lift (inclusion I q m)
    (pullback.snd q (quotientSpec (I ^ (m + 1))) ≫ quotientTransition I hmn) (by
      change pullback.fst q (quotientSpec (I ^ (m + 1))) ≫ q =
        (pullback.snd q (quotientSpec (I ^ (m + 1))) ≫ quotientTransition I hmn) ≫
          quotientSpec (I ^ (n + 1))
      rw [Category.assoc, quotientTransition_comp_base]
      exact pullback.condition)

/-- The transition commutes with the unchanged first projections to X. -/
theorem transition_comp_inclusion {m n : ℕ} (hmn : m ≤ n) :
    transition I q hmn ≫ inclusion I q n = inclusion I q m := by
  unfold transition inclusion NilpotentThickeningIdempotents.inclusion
  exact pullback.lift_fst _ _ _

/-- On the affine-base projection, the transition is the original quotient-factor map. -/
theorem transition_comp_snd {m n : ℕ} (hmn : m ≤ n) :
    transition I q hmn ≫ pullback.snd q (quotientSpec (I ^ (n + 1))) =
      pullback.snd q (quotientSpec (I ^ (m + 1))) ≫ quotientTransition I hmn := by
  unfold transition
  exact pullback.lift_snd _ _ _

/-- The original transition at an equal index is the identity. -/
theorem transition_refl (n : ℕ) : transition I q (le_refl n) = 𝟙 (thickening I q n) := by
  apply (cancel_mono (inclusion I q n)).mp
  rw [transition_comp_inclusion, Category.id_comp]

/-- The original quotient-induced transitions compose in the expected direction. -/
theorem transition_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    transition I q hkm ≫ transition I q hmn = transition I q (hkm.trans hmn) := by
  apply (cancel_mono (inclusion I q n)).mp
  rw [Category.assoc, transition_comp_inclusion, transition_comp_inclusion,
    transition_comp_inclusion]

/-- Each original transition is a closed immersion, as seen from the same closed embeddings in X. -/
instance transition_isClosedImmersion {m n : ℕ} (hmn : m ≤ n) :
    IsClosedImmersion (transition I q hmn) := by
  have : IsClosedImmersion (transition I q hmn ≫ inclusion I q n) := by
    rw [transition_comp_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (transition I q hmn) (inclusion I q n)

/-- Equality of the actual images in X proves surjectivity of the original transition. -/
instance transition_surjective {m n : ℕ} (hmn : m ≤ n) : Surjective (transition I q hmn) := by
  constructor
  intro y
  have hy : inclusion I q n y ∈ Set.range (inclusion I q m) := by
    rw [inclusion_range, ← inclusion_range I q n]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (inclusion I q n).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, transition_comp_inclusion]
  exact hx

/-- The actual transition, not an independently chosen map, is an underlying homeomorphism. -/
theorem transition_isHomeomorph {m n : ℕ} (hmn : m ≤ n) : IsHomeomorph (transition I q hmn) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(transition I q hmn).isClosedEmbedding.isEmbedding, (transition I q hmn).surjective⟩

/-- The original restriction along each transition is bijective on global idempotents. -/
theorem restriction_bijective {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (idempotentRestriction (transition I q hmn)) :=
  idempotentRestriction_bijective_of_isHomeomorph (transition I q hmn)
    (transition_isHomeomorph I q hmn)

/-- The actual restriction between the two original global-idempotent spaces. -/
def restrictionEquiv {m n : ℕ} (hmn : m ≤ n) :
    GlobalIdempotents (thickening I q n) ≃ GlobalIdempotents (thickening I q m) :=
  Equiv.ofBijective (idempotentRestriction (transition I q hmn)) (restriction_bijective I q hmn)

/-- The forward equivalence is the actual restriction map. -/
theorem restrictionEquiv_apply {m n : ℕ} (hmn : m ≤ n)
    (e : GlobalIdempotents (thickening I q n)) :
    restrictionEquiv I q hmn e = idempotentRestriction (transition I q hmn) e := rfl

/-- Lift a prescribed global idempotent on the original zeroth thickening to the n-th thickening. -/
def lift (e : GlobalIdempotents (thickening I q 0)) (n : ℕ) :
    GlobalIdempotents (thickening I q n) :=
  (restrictionEquiv I q (Nat.zero_le n)).symm e

/-- Each lifted idempotent has the prescribed restriction under the actual transition from X_0. -/
theorem lift_restrict_zero (e : GlobalIdempotents (thickening I q 0)) (n : ℕ) :
    idempotentRestriction (transition I q (Nat.zero_le n)) (lift I q e n) = e :=
  (restrictionEquiv I q (Nat.zero_le n)).apply_symm_apply e

/-- The zeroth member of the family is the original prescribed idempotent. -/
theorem lift_zero (e : GlobalIdempotents (thickening I q 0)) : lift I q e 0 = e := by
  have h := lift_restrict_zero I q e 0
  rw [transition_refl] at h
  exact h

/-- Uniqueness of the actual restriction lifts proves their full compatibility. -/
theorem lift_compatible (e : GlobalIdempotents (thickening I q 0))
    {m n : ℕ} (hmn : m ≤ n) :
    idempotentRestriction (transition I q hmn) (lift I q e n) = lift I q e m := by
  apply (restrictionEquiv I q (Nat.zero_le m)).injective
  change idempotentRestriction (transition I q (Nat.zero_le m))
      (idempotentRestriction (transition I q hmn) (lift I q e n)) =
    idempotentRestriction (transition I q (Nat.zero_le m)) (lift I q e m)
  rw [← idempotentRestriction_comp, transition_comp, lift_restrict_zero, lift_restrict_zero]

/-- The compatible family uses exactly the original maps on global sections. -/
theorem lift_compatible_appTop (e : GlobalIdempotents (thickening I q 0))
    {m n : ℕ} (hmn : m ≤ n) :
    (transition I q hmn).appTop (lift I q e n).1 = (lift I q e m).1 :=
  congrArg Subtype.val (lift_compatible I q e hmn)

/-- A prescribed idempotent on X_0 has a unique family on all actual thickenings,
compatible under every original transition. -/
theorem existsUnique_compatible_lifts (e : GlobalIdempotents (thickening I q 0)) :
    ∃! a : (n : ℕ) → GlobalIdempotents (thickening I q n),
      a 0 = e ∧ ∀ (m n : ℕ) (hmn : m ≤ n),
        idempotentRestriction (transition I q hmn) (a n) = a m := by
  refine ⟨lift I q e, ⟨lift_zero I q e, fun _ _ hmn => lift_compatible I q e hmn⟩, ?_⟩
  intro a ha
  funext n
  apply (restrictionEquiv I q (Nat.zero_le n)).injective
  change idempotentRestriction (transition I q (Nat.zero_le n)) (a n) =
    idempotentRestriction (transition I q (Nat.zero_le n)) (lift I q e n)
  rw [ha.2 0 n (Nat.zero_le n), ha.1, lift_restrict_zero]

end PrimeGap182.TypeIII.InfinitesimalIdempotentTower

#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.quotientSpec_range
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.quotientTransition
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.quotientTransition_comp_base
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.thickening
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.inclusion
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.inclusion_isClosedImmersion
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.inclusion_range
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_comp_inclusion
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_comp_snd
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_refl
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_comp
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_isClosedImmersion
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_surjective
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.transition_isHomeomorph
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.restriction_bijective
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.restrictionEquiv
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.restrictionEquiv_apply
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.lift
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.lift_restrict_zero
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.lift_zero
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.lift_compatible
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.lift_compatible_appTop
#print axioms PrimeGap182.TypeIII.InfinitesimalIdempotentTower.existsUnique_compatible_lifts
