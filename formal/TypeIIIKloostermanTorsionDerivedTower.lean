import TypeIIIArtinSchreierLimitSheaf
import TypeIIIEtaleDerivedDirectImage
import TypeIIIInjectiveResolutionAdditivity

/-!
# The actual finite-level system under relative derived direct image

The original phase sheaves, viewed as modules over the actual coefficient
limit, form a coherent inverse system. Applying the constructed relative
derived-image functor gives a genuine inverse system on the original
parameter line in every cohomological degree.

Every level remains annihilated by its stated power of ℓ. This follows
from the original finite coefficient action and the proved additivity of
the actual derived functors. No finiteness, concentration, comparison
with derived images computed in a different coefficient category,
adic-cohomology comparison, or trace formula is asserted.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP

/-- The actual compactified derived-image functor is additive. -/
instance kloostermanCompactifiedDerivedImage_additive (p : ℕ) (E : Type) [Ring E] (d : ℕ) :
    (kloostermanCompactifiedDerivedImage p E d).Additive := by
  change (kloostermanPhaseExtensionByZero p E ⋙
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p) E).rightDerived d).Additive
  infer_instance

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

set_option backward.isDefEq.respectTransparency false in
/-- The original level-n sheaf is annihilated by ℓ^(n+1), including after actual scalar restriction. -/
theorem torsionArtinSchreierLimitModuleSheaf_nsmul_id
    {R : Type} [CommRing R] [CharP R p] (f : R) (n : ℕ) :
    (ell ^ (n + 1)) • (𝟙 (torsionArtinSchreierLimitModuleSheaf p ell hne f n)) = 0 := by
  apply Sheaf.hom_ext
  ext U x
  change (ell ^ (n + 1)) •
    (show (torsionArtinSchreierSheaf p ell hne n f).obj.obj U from x) = 0
  let y : (torsionArtinSchreierSheaf p ell hne n f).obj.obj U := x
  have hc : (ell ^ (n + 1) : TorsionCoefficientRing p ell n) = 0 := by
    rw [← Nat.cast_pow]
    exact CharP.cast_eq_zero (TorsionCoefficientRing p ell n) (ell ^ (n + 1))
  have h : (ell ^ (n + 1) : TorsionCoefficientRing p ell n) • y = 0 := by
    rw [hc, zero_smul]
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using h

/-- In each degree, the original finite phase system gives an actual inverse system
of relative derived images on the same parameter line. -/
def kloostermanTorsionDerivedTower (d : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) :=
  torsionArtinSchreierLimitModuleTower p ell hne (kloostermanPhaseFunction p) ⋙
    kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d

/-- Every object is the actual constructed R^d barπ_* j! of the original finite-level sheaf. -/
theorem kloostermanTorsionDerivedTower_obj (d n : ℕ) :
    (kloostermanTorsionDerivedTower p ell hne d).obj (op n) =
      (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).obj
        (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the actual additive derived functor preserves the original torsion exponent. -/
theorem kloostermanTorsionDerivedTower_nsmul_id (d n : ℕ) :
    (ell ^ (n + 1)) • (𝟙 ((kloostermanTorsionDerivedTower p ell hne d).obj (op n))) = 0 := by
  let G := kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d
  have h := congrArg G.map
    (torsionArtinSchreierLimitModuleSheaf_nsmul_id p ell hne (kloostermanPhaseFunction p) n)
  rw [Functor.map_nsmul,
    G.map_id (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n),
    Functor.map_zero] at h
  exact h

/-- The asserted torsion exponent holds on each actual section of the derived image. -/
theorem kloostermanTorsionDerivedTower_nsmul_section (d n : ℕ)
    (U : (Spec (.of (Polynomial (ZMod p)))).Etaleᵒᵖ)
    (x : ((kloostermanTorsionDerivedTower p ell hne d).obj (op n)).obj.obj U) :
    (ell ^ (n + 1)) • x = 0 := by
  have h := congrArg (fun g => g.hom.app U x)
    (kloostermanTorsionDerivedTower_nsmul_id p ell hne d n)
  exact h

#print axioms kloostermanCompactifiedDerivedImage_additive
#print axioms torsionArtinSchreierLimitModuleSheaf_nsmul_id
#print axioms kloostermanTorsionDerivedTower
#print axioms kloostermanTorsionDerivedTower_obj
#print axioms kloostermanTorsionDerivedTower_nsmul_id
#print axioms kloostermanTorsionDerivedTower_nsmul_section

end PrimeGap182.TypeIII
