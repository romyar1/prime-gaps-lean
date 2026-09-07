import TypeIIIKloostermanFiberBaseChange
import TypeIIIKloostermanTorsionDerivedTower

/-!
# The original finite-coefficient system on the actual proper fiber

Applying the actual fiber-cohomology functor to the existing finite
phase system gives an inverse system of modules over the original
coefficient limit.  Each level is killed by its stated power of ℓ.
The original geometric base-change maps assemble into a natural map
from the stalks of the relative derived-image system to this system.

The existing cone from the limit-coefficient phase sheaf also maps to a
cone on fiber cohomology.  No assertion that this cone is a limit, that
the base-change map is invertible, or that these groups have been
identified with adic cohomology is made.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] kloostermanPhaseRing_charP

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Spec (.of (Polynomial (ZMod p))))

/-- The original relative finite-level derived images evaluated at the actual geometric point. -/
def kloostermanTorsionDerivedStalkTower (d : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{0} (TorsionCoefficientLimit p ell) :=
  kloostermanTorsionDerivedTower p ell hne d ⋙
    (Scheme.pointSmallEtale s).sheafFiber

/-- The original finite phase system under actual cohomology on the specified proper fiber. -/
def kloostermanTorsionFiberCohomologyTower (d : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{0} (TorsionCoefficientLimit p ell) :=
  torsionArtinSchreierLimitModuleTower p ell hne (kloostermanPhaseFunction p) ⋙
    kloostermanFiberCompactCohomology p s (TorsionCoefficientLimit p ell) d

omit [IsSepClosed Ω] in
/-- Every level is actual fiber cohomology of the unchanged finite phase sheaf. -/
theorem kloostermanTorsionFiberCohomologyTower_obj (d n : ℕ) :
    (kloostermanTorsionFiberCohomologyTower p ell hne s d).obj (op n) =
      (kloostermanFiberCompactCohomology p s (TorsionCoefficientLimit p ell) d).obj
        (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n) := rfl

omit [IsSepClosed Ω] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual additive fiber-cohomology functor preserves the original finite torsion exponent. -/
theorem kloostermanTorsionFiberCohomologyTower_nsmul_id (d n : ℕ) :
    (ell ^ (n + 1)) •
        (𝟙 ((kloostermanTorsionFiberCohomologyTower p ell hne s d).obj (op n))) = 0 := by
  let G := kloostermanFiberCompactCohomology p s (TorsionCoefficientLimit p ell) d
  have h := congrArg G.map
    (torsionArtinSchreierLimitModuleSheaf_nsmul_id p ell hne (kloostermanPhaseFunction p) n)
  rw [Functor.map_nsmul,
    G.map_id (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n),
    Functor.map_zero] at h
  exact h

omit [IsSepClosed Ω] in
/-- Every element of the actual fiber-cohomology module has the stated torsion exponent. -/
theorem kloostermanTorsionFiberCohomologyTower_nsmul (d n : ℕ)
    (x : (kloostermanTorsionFiberCohomologyTower p ell hne s d).obj (op n)) :
    (ell ^ (n + 1)) • x = 0 := by
  have h := congrArg (fun f => f x)
    (kloostermanTorsionFiberCohomologyTower_nsmul_id p ell hne s d n)
  exact h

/-- The original fiber-base-change maps form a natural transformation of the actual finite systems. -/
def kloostermanTorsionFiberBaseChange (d : ℕ) :
    kloostermanTorsionDerivedStalkTower p ell hne s d ⟶
      kloostermanTorsionFiberCohomologyTower p ell hne s d :=
  Functor.whiskerLeft
    (torsionArtinSchreierLimitModuleTower p ell hne (kloostermanPhaseFunction p))
    (kloostermanFiberBaseChange p s (TorsionCoefficientLimit p ell) d)

/-- The component is the original base-change map on the original finite-level phase sheaf. -/
theorem kloostermanTorsionFiberBaseChange_app (d n : ℕ) :
    (kloostermanTorsionFiberBaseChange p ell hne s d).app (op n) =
      (kloostermanFiberBaseChange p s (TorsionCoefficientLimit p ell) d).app
        (torsionArtinSchreierLimitModuleSheaf p ell hne (kloostermanPhaseFunction p) n) := rfl

/-- Reduction of the actual coefficient level commutes with the same geometric comparison. -/
theorem kloostermanTorsionFiberBaseChange_reduction (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (kloostermanTorsionDerivedStalkTower p ell hne s d).map (homOfLE hmn).op ≫
        (kloostermanTorsionFiberBaseChange p ell hne s d).app (op m) =
      (kloostermanTorsionFiberBaseChange p ell hne s d).app (op n) ≫
        (kloostermanTorsionFiberCohomologyTower p ell hne s d).map (homOfLE hmn).op :=
  (kloostermanTorsionFiberBaseChange p ell hne s d).naturality (homOfLE hmn).op

/-- The actual compatible cone from the limit-coefficient phase sheaf after fiber cohomology. -/
def kloostermanTorsionFiberCohomologyCone (d : ℕ) :
    Cone (kloostermanTorsionFiberCohomologyTower p ell hne s d) :=
  (kloostermanFiberCompactCohomology p s (TorsionCoefficientLimit p ell) d).mapCone
    (limitArtinSchreierCone p ell hne (kloostermanPhaseFunction p))

omit [IsSepClosed Ω] in
/-- Its vertex is the actual fiber cohomology of the original limit-coefficient sheaf. -/
theorem kloostermanTorsionFiberCohomologyCone_pt (d : ℕ) :
    (kloostermanTorsionFiberCohomologyCone p ell hne s d).pt =
      (kloostermanFiberCompactCohomology p s (TorsionCoefficientLimit p ell) d).obj
        (limitArtinSchreierSheaf p ell hne (kloostermanPhaseFunction p)) := rfl

#print axioms kloostermanTorsionDerivedStalkTower
#print axioms kloostermanTorsionFiberCohomologyTower
#print axioms kloostermanTorsionFiberCohomologyTower_obj
#print axioms kloostermanTorsionFiberCohomologyTower_nsmul_id
#print axioms kloostermanTorsionFiberCohomologyTower_nsmul
#print axioms kloostermanTorsionFiberBaseChange
#print axioms kloostermanTorsionFiberBaseChange_app
#print axioms kloostermanTorsionFiberBaseChange_reduction
#print axioms kloostermanTorsionFiberCohomologyCone
#print axioms kloostermanTorsionFiberCohomologyCone_pt

end PrimeGap182.TypeIII
