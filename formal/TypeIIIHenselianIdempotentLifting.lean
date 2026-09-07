import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Idempotents and clopens of an actual henselian pair

For the existing Mathlib class `HenselianRing R I`, reduction from R
to R / I is a bijection on idempotents.  Existence follows by applying
the defining simple-root property to X² - X; uniqueness uses only
I ⊆ Jac(R).  The derivative at a residue idempotent is a unit in every
characteristic, including characteristic two.

The induced order isomorphism on clopen subsets is literally inverse
image under Spec(R / I) ⟶ Spec(R), as proved by its compatibility with
the existing idempotent/clopen correspondence.  No localness,
Noetherian assumption, or nontriviality assumption is imposed on R.
This file does not assert stability of henselian pairs under integral
extension, or lifting of clopens on a proper nonaffine scheme.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.HenselianIdempotentLifting

open Polynomial TopologicalSpace

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- At any idempotent, the derivative of X² - X is its own inverse. -/
theorem derivative_isUnit (a : R) (ha : IsIdempotentElem a) : IsUnit (2 * a - 1) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨2 * a - 1, ?_⟩
  calc
    (2 * a - 1) * (2 * a - 1) = 4 * (a * a - a) + 1 := by ring
    _ = 1 := by rw [ha.eq]; ring

/-- The actual quotient ring map on idempotent elements. -/
def idempotentReduction (a : {a : R // IsIdempotentElem a}) :
    {a : R ⧸ I // IsIdempotentElem a} :=
  ⟨Ideal.Quotient.mk I a, a.2.map (Ideal.Quotient.mk I)⟩

/-- Reduction has its literal quotient-map value. -/
theorem idempotentReduction_apply (a : {a : R // IsIdempotentElem a}) :
    (idempotentReduction R I a).1 = Ideal.Quotient.mk I a := rfl

/-- Uniqueness of an idempotent lift uses only the Jacobson condition. -/
theorem idempotentReduction_injective_of_le_jacobson
    (hI : I ≤ Ideal.jacobson ⊥) : Function.Injective (idempotentReduction R I) := by
  let : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hI
  intro a b h
  have hab : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := congrArg Subtype.val h
  have hq : Ideal.Quotient.mk I (a.1 + b.1 - 1) = 2 * Ideal.Quotient.mk I a.1 - 1 := by
    rw [map_sub, map_add, map_one, ← hab]
    ring
  have hu : IsUnit (a.1 + b.1 - 1) := IsUnit.of_map (Ideal.Quotient.mk I) (a.1 + b.1 - 1) (by
    rw [hq]
    exact derivative_isUnit (R ⧸ I) (Ideal.Quotient.mk I a) (a.2.map (Ideal.Quotient.mk I)))
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hu.mul_left_eq_zero.mp
  calc
    (a.1 - b.1) * (a.1 + b.1 - 1) = (a.1 * a.1 - a.1) - (b.1 * b.1 - b.1) := by ring
    _ = 0 := by rw [a.2.eq, b.2.eq]; ring

variable [HenselianRing R I]

/-- Actual simple-root lifting gives an idempotent above every residue idempotent. -/
theorem idempotentReduction_surjective : Function.Surjective (idempotentReduction R I) := by
  rintro ⟨a, ha⟩
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hm : (X ^ 2 - X : R[X]).Monic := by
    simpa [pow_two, mul_sub] using (monic_X : (X : R[X]).Monic).mul (monic_X_sub_C (1 : R))
  have hf : (X ^ 2 - X : R[X]).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [pow_two, ha.eq]
  have hd : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : R[X]).derivative.eval a₀)) := by
    simpa [derivative_sub, derivative_X_pow, ← one_add_one_eq_two] using derivative_isUnit (R ⧸ I)
      (Ideal.Quotient.mk I a₀) ha
  obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X) hm a₀ hf hd
  have hb' : IsIdempotentElem b := by
    simpa [Polynomial.IsRoot, pow_two, sub_eq_zero, IsIdempotentElem] using hb
  exact ⟨⟨b, hb'⟩, Subtype.ext (Ideal.Quotient.eq.mpr hba)⟩

/-- Reduction of idempotents is bijective for the given henselian pair. -/
theorem idempotentReduction_bijective : Function.Bijective (idempotentReduction R I) :=
  ⟨idempotentReduction_injective_of_le_jacobson R I HenselianRing.jac,
    idempotentReduction_surjective R I⟩

/-- The bijection packages the actual quotient-map reduction. -/
def idempotentReductionEquiv :
    {a : R // IsIdempotentElem a} ≃ {a : R ⧸ I // IsIdempotentElem a} :=
  Equiv.ofBijective (idempotentReduction R I) (idempotentReduction_bijective R I)

/-- The forward equivalence is the original reduction function. -/
theorem idempotentReductionEquiv_apply (a : {a : R // IsIdempotentElem a}) :
    idempotentReductionEquiv R I a = idempotentReduction R I a := rfl

/-- The inverse returns an actual lift with the specified residue. -/
theorem idempotentReductionEquiv_symm_spec (a : {a : R ⧸ I // IsIdempotentElem a}) :
    Ideal.Quotient.mk I ((idempotentReductionEquiv R I).symm a).1 = a.1 :=
  congrArg Subtype.val ((idempotentReductionEquiv R I).apply_symm_apply a)

/-- Each prescribed residue idempotent has a unique idempotent lift in R. -/
theorem existsUnique_idempotent_lift (a : R ⧸ I) (ha : IsIdempotentElem a) :
    ∃! b : R, IsIdempotentElem b ∧ Ideal.Quotient.mk I b = a := by
  obtain ⟨b, hb⟩ := idempotentReduction_surjective R I ⟨a, ha⟩
  refine ⟨b.1, ⟨b.2, congrArg Subtype.val hb⟩, ?_⟩
  intro c hc
  have hcb : idempotentReduction R I ⟨c, hc.1⟩ = idempotentReduction R I b :=
    (Subtype.ext hc.2).trans hb.symm
  exact congrArg Subtype.val ((idempotentReduction_bijective R I).injective hcb)

omit [HenselianRing R I] in
/-- Pullback of clopens by the actual prime-spectrum map of the quotient. -/
def clopenReduction (U : Clopens (PrimeSpectrum R)) : Clopens (PrimeSpectrum (R ⧸ I)) :=
  ⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' (U : Set (PrimeSpectrum R)),
    U.isClopen.preimage (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk I))⟩

omit [HenselianRing R I] in
/-- Its carrier is exactly the inverse image under Spec(R / I) ⟶ Spec(R). -/
theorem clopenReduction_coe (U : Clopens (PrimeSpectrum R)) :
    (clopenReduction R I U : Set (PrimeSpectrum (R ⧸ I))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' (U : Set (PrimeSpectrum R)) := rfl

omit [HenselianRing R I] in
/-- The actual clopen pullback agrees with reduction of its defining idempotent. -/
theorem clopenReduction_idempotent (a : {a : R // IsIdempotentElem a}) :
    clopenReduction R I (PrimeSpectrum.isIdempotentElemEquivClopens a) =
      PrimeSpectrum.isIdempotentElemEquivClopens (idempotentReduction R I a) := by
  ext x
  rfl

/-- Clopen pullback along the actual quotient spectrum map is bijective. -/
theorem clopenReduction_bijective : Function.Bijective (clopenReduction R I) := by
  constructor
  · intro U V h
    obtain ⟨a, rfl⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).surjective U
    obtain ⟨b, rfl⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).surjective V
    rw [clopenReduction_idempotent, clopenReduction_idempotent] at h
    exact congrArg PrimeSpectrum.isIdempotentElemEquivClopens
      ((idempotentReduction_bijective R I).injective
        (PrimeSpectrum.isIdempotentElemEquivClopens.injective h))
  · intro U
    obtain ⟨a, rfl⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := R ⧸ I)).surjective U
    obtain ⟨b, rfl⟩ := idempotentReduction_surjective R I a
    exact ⟨PrimeSpectrum.isIdempotentElemEquivClopens b, clopenReduction_idempotent R I b⟩

/-- The clopen order isomorphism has the actual pullback as its forward function. -/
def clopenReductionOrderIso : Clopens (PrimeSpectrum R) ≃o Clopens (PrimeSpectrum (R ⧸ I)) where
  toEquiv := Equiv.ofBijective (clopenReduction R I) (clopenReduction_bijective R I)
  map_rel_iff' := by
    intro U V
    constructor
    · intro h
      apply inf_eq_left.mp
      apply (clopenReduction_bijective R I).injective
      change clopenReduction R I U ⊓ clopenReduction R I V = clopenReduction R I U
      exact inf_eq_left.mpr h
    · intro h x hx
      exact h hx

/-- The forward order isomorphism is the unchanged clopen pullback. -/
theorem clopenReductionOrderIso_apply (U : Clopens (PrimeSpectrum R)) :
    clopenReductionOrderIso R I U = clopenReduction R I U := rfl

/-- The inverse lifts a specified clopen with equality under the original pullback. -/
theorem clopenReductionOrderIso_symm_spec (U : Clopens (PrimeSpectrum (R ⧸ I))) :
    clopenReduction R I ((clopenReductionOrderIso R I).symm U) = U :=
  (clopenReductionOrderIso R I).apply_symm_apply U

#print axioms derivative_isUnit
#print axioms idempotentReduction
#print axioms idempotentReduction_apply
#print axioms idempotentReduction_injective_of_le_jacobson
#print axioms idempotentReduction_surjective
#print axioms idempotentReduction_bijective
#print axioms idempotentReductionEquiv
#print axioms idempotentReductionEquiv_apply
#print axioms idempotentReductionEquiv_symm_spec
#print axioms existsUnique_idempotent_lift
#print axioms clopenReduction
#print axioms clopenReduction_coe
#print axioms clopenReduction_idempotent
#print axioms clopenReduction_bijective
#print axioms clopenReductionOrderIso
#print axioms clopenReductionOrderIso_apply
#print axioms clopenReductionOrderIso_symm_spec

end PrimeGap182.TypeIII.HenselianIdempotentLifting
