import TypeIIIArithmeticSourceTransport

/-!
# Transport local Frobenius covariance through the original specialization

The local Weil/inertia conjugation law is a general input. The original
curve-input law follows using the same representation equivalence and
Frobenius comparison already used by the primitive arithmetic sources.
No original-family covariance is supplied, and Frobenius is not assumed
to commute with inertia.
-/

noncomputable section
open CategoryTheory

namespace PrimeGap182.TypeIII.ArithmeticCovarianceFromSpecialization

open ArithmeticSourceTransport

universe u v a b c

variable {Input : Type u} [Category.{a} Input]
  {Local : Type v} [Category.{b} Local] {G : Type c} [Group G]
  (J : Local ⥤ FDRep ℂ G) (along : Input ⥤ Local)
  (zero : Input → FDRep ℂ G)
  (originalFr : ∀ A, (zero A).V ≃ₗ[ℂ] (zero A).V)
  (LF : LocalFrobenius J)
  (SC : SpecializationComparison J along zero originalFr LF)
  (conjugation : G →* G)
  (localCovariance : ∀ A g v,
    LF.action A ((J.obj A).ρ g v) =
      (J.obj A).ρ (conjugation g) (LF.action A v))

include SC localCovariance in
/-- The same specialization comparison transports the conjugation law
to every original input. The Frobenius and inertia operators are retained. -/
theorem covariance (A : Input) (g : G) (v : (zero A).V) :
    originalFr A ((zero A).ρ g v) =
      (zero A).ρ (conjugation g) (originalFr A v) := by
  let e := SC.comparison A
  have he (s : G) (x : (zero A).V) :
      e ((zero A).ρ s x) = (J.obj (along.obj A)).ρ s (e x) :=
    LinearMap.congr_fun (e.isIntertwining' s) x
  apply e.toLinearEquiv.injective
  calc
    e (originalFr A ((zero A).ρ g v)) =
        LF.action (along.obj A) (e ((zero A).ρ g v)) := SC.frobenius A _
    _ = LF.action (along.obj A) ((J.obj (along.obj A)).ρ g (e v)) :=
      congrArg (LF.action (along.obj A)) (he g v)
    _ = (J.obj (along.obj A)).ρ (conjugation g) (LF.action (along.obj A) (e v)) :=
      localCovariance _ _ _
    _ = (J.obj (along.obj A)).ρ (conjugation g) (e (originalFr A v)) :=
      congrArg ((J.obj (along.obj A)).ρ (conjugation g)) (SC.frobenius A v).symm
    _ = e ((zero A).ρ (conjugation g) (originalFr A v)) :=
      (he (conjugation g) (originalFr A v)).symm

end PrimeGap182.TypeIII.ArithmeticCovarianceFromSpecialization

#print axioms PrimeGap182.TypeIII.ArithmeticCovarianceFromSpecialization.covariance
