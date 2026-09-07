import TypeIIIArtinSchreierBocksteinTransitions
import TypeIIIKloostermanBockstein

/-!
# Naturality of the original Kloosterman Bockstein maps

The original coefficient-sequence transition is mapped through the
actual extension by zero. Naturality of the existing derived connecting
morphism then gives the complementary ell power on the next ordinary
derived image. All finite reduction maps and connecting morphisms are
the original constructions.

The source derived images remain ordinary sheaf cohomology with discrete
limit coefficients. No adic comparison is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP HasDerivedCategory.standard

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The actual j! applied to the original coefficient-sequence transition. -/
def kloostermanBocksteinExtendedTransition {m n : ℕ} (hmn : m ≤ n) :
    kloostermanBocksteinExtendedSequence p ell hne n ⟶
      kloostermanBocksteinExtendedSequence p ell hne m :=
  (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).mapShortComplex.map
    (limitArtinSchreierBocksteinTransition p ell hne (kloostermanPhaseFunction p) hmn)

/-- Exact extension by zero retains the complementary integer multiplication. -/
theorem kloostermanBocksteinExtendedTransition_τ₁ {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanBocksteinExtendedTransition p ell hne hmn).τ₁ =
      (ell ^ (n - m)) • 𝟙
        ((kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).obj
          (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p))) := by
  change (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
    ((ell ^ (n - m)) •
      𝟙 (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p))) = _
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]

/-- The middle transition after extension remains the actual identity. -/
theorem kloostermanBocksteinExtendedTransition_τ₂ {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanBocksteinExtendedTransition p ell hne hmn).τ₂ =
      𝟙 ((kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).obj
        (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p))) :=
  CategoryTheory.Functor.map_id _ _

/-- The right transition is the original finite reduction mapped by the actual j!. -/
@[simp] theorem kloostermanBocksteinExtendedTransition_τ₃ {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanBocksteinExtendedTransition p ell hne hmn).τ₃ =
      (kloostermanPhaseExtensionByZero p (TorsionCoefficientLimit p ell)).map
        (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p)
          hmn) := rfl

/-- Naturality of the original connecting morphism for the actual extended
sequence transition produces the complementary power in the next degree. -/
theorem kloostermanBocksteinConnecting_naturality (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
        (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p)
          hmn) ≫
      kloostermanBocksteinConnecting p ell hne d m =
    kloostermanBocksteinConnecting p ell hne d n ≫
      ((ell ^ (n - m)) • 𝟙 (kloostermanLimitDerivedImage p ell hne (d + 1))) := by
  have h := rightDerivedConnectingHom_naturality
    (EtaleDirectImage.functor (kloostermanCompactificationProjection p)
      (TorsionCoefficientLimit p ell))
    (kloostermanBocksteinExtendedSequence_shortExact p ell hne n)
    (kloostermanBocksteinExtendedSequence_shortExact p ell hne m)
    (kloostermanBocksteinExtendedTransition p ell hne hmn) d
  change (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
      (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p)
        hmn) ≫ kloostermanBocksteinConnecting p ell hne d m =
    kloostermanBocksteinConnecting p ell hne d n ≫
      ((EtaleDirectImage.functor (kloostermanCompactificationProjection p)
        (TorsionCoefficientLimit p ell)).rightDerived (d + 1)).map
          (kloostermanBocksteinExtendedTransition p ell hne hmn).τ₁ at h
  rw [kloostermanBocksteinExtendedTransition_τ₁, CategoryTheory.Functor.map_nsmul,
    CategoryTheory.Functor.map_id] at h
  exact h

/-- The original ordinary derived reduction maps are compatible with every
original finite transition. -/
theorem kloostermanBocksteinReduction_comp (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    kloostermanBocksteinReduction p ell hne d n ≫
      (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
        (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p)
          hmn) =
    kloostermanBocksteinReduction p ell hne d m := by
  change (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
      (limitArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) n) ≫
    (kloostermanCompactifiedDerivedImage p (TorsionCoefficientLimit p ell) d).map
      (torsionArtinSchreierLimitModuleReduction p ell hne (kloostermanPhaseFunction p)
        hmn) = _
  rw [← CategoryTheory.Functor.map_comp, limitArtinSchreierReduction_comp]
  rfl

#print axioms kloostermanBocksteinExtendedTransition
#print axioms kloostermanBocksteinExtendedTransition_τ₁
#print axioms kloostermanBocksteinExtendedTransition_τ₂
#print axioms kloostermanBocksteinExtendedTransition_τ₃
#print axioms kloostermanBocksteinConnecting_naturality
#print axioms kloostermanBocksteinReduction_comp

end PrimeGap182.TypeIII
