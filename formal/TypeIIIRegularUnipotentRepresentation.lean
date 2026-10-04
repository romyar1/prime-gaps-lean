import TypeIIIBoundaryFromSourceModels

/-!
# The literal regular-unipotent representation

Construct the action exp(tN) = 1 + tN + (t^2/2)N^2 and prove the group
law. Composing with a nonzero tame additive character gives the common
rank-three model used by the boundary calculation. The representation
and its RegularModel record are constructed, not additional assumptions.
Identifying the single Kloosterman sources with this model remains the
published one-variable geometric input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical Matrix

namespace PrimeGap182.TypeIII.RegularUnipotentRepresentation

open RegularUnipotentBoundary

universe u v
variable {k : Type u} [Field k] [CharZero k]

def exponentialMatrix (t : k) : Matrix (Fin 3) (Fin 3) k := regularMatrix t (t ^ 2 / 2)

omit [CharZero k] in
theorem exponentialMatrix_zero : exponentialMatrix (0 : k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentialMatrix, regularMatrix, jordanThreeCoordinates]

/-- The finite exponential really obeys the additive group law. -/
theorem exponentialMatrix_add (s t : k) :
    exponentialMatrix (s + t) = exponentialMatrix s * exponentialMatrix t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exponentialMatrix, regularMatrix, jordanThreeCoordinates,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- An actual representation of the additive coefficient group, written
using Multiplicative so that it fits the existing inertia interface. -/
def exponentialRepresentation : Representation k (Multiplicative k) (Fin 3 → k) where
  toFun g := Matrix.toLin' (exponentialMatrix g.toAdd)
  map_one' := by
    change Matrix.toLin' (exponentialMatrix (0 : k)) = 1
    rw [exponentialMatrix_zero, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    change Matrix.toLin' (exponentialMatrix (g.toAdd + h.toAdd)) = _
    rw [exponentialMatrix_add, Matrix.toLin'_mul]
    rfl

variable {G : Type v} [Group G]

/-- Pull the genuine representation back along the tame character. -/
def tameRepresentation (tame : G →* Multiplicative k) : Representation k G (Fin 3 → k) :=
  (exponentialRepresentation (k := k)).comp tame

/-- Nonzero tame monodromy supplies regularity; all action formulas and
the representation laws have already been proved. -/
def tameRegularModel (tame : G →* Multiplicative k)
    (h : ∃ g, (tame g).toAdd ≠ 0) : RegularModel (tameRepresentation tame) where
  linearCoefficient g := (tame g).toAdd
  quadraticCoefficient g := (tame g).toAdd ^ 2 / 2
  action _ := LinearMap.toMatrix'_toLin' _
  regular := h

section PhysicalRank

open CategoryTheory CategoryTheory.Limits PublishedPhysicalConstruction
open BoundaryFromSourceModels GeometricCoreRank

universe w z a b c d
variable {Input : Type w} {Point : Type z} {C : Type a}
  [Category.{b} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{a} ℂ}
  {G0 : Type c} [Group G0] {Ginf : Type d} [Group Ginf]
  {S : BoundarySequence D H F}

/-- The physical rank endpoint with the regular representation and its
action laws constructed from the nonzero tame character. -/
theorem core_rank_six_from_tame_sources
    (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F S)
    (K : KloostermanInputData D) (R : CurveRules D)
    (tame : G0 →* Multiplicative ℂ) (htame : ∃ g, (tame g).toAdd ≠ 0)
    (hfirst : Representation.Equiv (Z.zero K.first).ρ (tameRepresentation tame))
    (hsecond : Representation.Equiv (Z.zero K.second).ρ (tameRepresentation tame))
    (hadditive : Representation.Equiv (Z.zero K.additive).ρ (Representation.trivial ℂ G0 ℂ))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (point : Point) (V : GeometricFiberRules D H F point) :
    Module.finrank ℂ (F.obj (parabolicCore H K.input)) = 6 :=
  core_rank_six_from_sources Z K R (tameRegularModel tame htame)
    hfirst hsecond hadditive point V

end PhysicalRank

end PrimeGap182.TypeIII.RegularUnipotentRepresentation

#print axioms PrimeGap182.TypeIII.RegularUnipotentRepresentation.exponentialMatrix_zero
#print axioms PrimeGap182.TypeIII.RegularUnipotentRepresentation.exponentialMatrix_add
#print axioms PrimeGap182.TypeIII.RegularUnipotentRepresentation.exponentialRepresentation
#print axioms PrimeGap182.TypeIII.RegularUnipotentRepresentation.tameRepresentation
#print axioms PrimeGap182.TypeIII.RegularUnipotentRepresentation.tameRegularModel
#print axioms PrimeGap182.TypeIII.RegularUnipotentRepresentation.core_rank_six_from_tame_sources
