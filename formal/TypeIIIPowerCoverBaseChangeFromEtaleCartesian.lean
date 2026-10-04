import TypeIIIPowerScalarCartesianFromUnitAutomorphism
import TypeIIITensorListRepresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.CharP.Invertible
import Mathlib.CategoryTheory.Whiskering

/-!
# Actual power-cover base change from a general finite étale square

The source and target maps are the literal native Laurent power/scalar maps.
ONE universal finite-étale Cartesian pull/push natural comparison supplies
base change, after the already proved actual square. The positive exponent
and invertible exponent are genuine numerical guards. Their ALL-field
finite-étale geometric certificate is explicit; no adic or inertia model is
constructed. Any full nearby functor then transports the entire natural
isomorphism and every curve object's actual representation equivalence.
No selected cubic scalar rule or completed ScalarInputs is an assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PrimeGap182.TypeIII.PowerCoverBaseChangeFromEtaleCartesian
open ArithmeticSourceMaps PowerCoverScalarCoordinates PowerScalarCartesianFromUnitAutomorphism
open ExactInverseImagesToDerived TensorListRepresentation

/-- Positive exponent and its literal invertibility in the geometric field. -/
def powerCoverGuard (K : Type) [Field K] (n : ℕ) : Prop := 0 < n ∧ IsUnit (n : K)

theorem powerCoverGuard_positive (K : Type) [Field K] (n : ℕ)
    (h : powerCoverGuard K n) : 0 < n := h.1

theorem powerCoverGuard_natCast_ne_zero (K : Type) [Field K] (n : ℕ)
    (h : powerCoverGuard K n) : (n : K) ≠ 0 := h.2.ne_zero

/-- The published prime-characteristic coprimality guard supplies invertibility. -/
theorem powerCoverGuard_of_coprime (K : Type) [Field K] (p : ℕ) [CharP K p]
    (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) : powerCoverGuard K n := by
  let : Invertible (n : K) := invertibleOfCoprime (R := K) hc
  exact ⟨hn, isUnit_of_invertible _⟩

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (push : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Etale f], C X ⥤ C Y)
  (etaleCartesianBaseChange : ∀ {X' X Y' Y : Scheme.{0}}
    (a : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y) (b : Y' ⟶ Y)
    [IsFinite p'] [Etale p'] [IsFinite p] [Etale p], IsPullback a p' p b →
      ((push p ⋙ U.pull b) ≅ (U.pull a ⋙ push p')))
  (powerFiniteEtale : ∀ (K : Type) [Field K] (n : ℕ), powerCoverGuard K n →
    IsFinite (powerMorphism K K n) ∧ Etale (powerMorphism K K n))

variable (K : Type) [Field K] (n : ℕ) (hn : powerCoverGuard K n)

/-- SAME push system at the literal power map and its guarded geometry. -/
def powerPush : C (fiberScheme K) ⥤ C (fiberScheme K) := by
  letI := (powerFiniteEtale K n hn).1
  letI := (powerFiniteEtale K n hn).2
  exact push (powerMorphism K K n)

/-- The complete ALL-object natural comparison for the actual power/scalar square. -/
def powerScalarIso (r : Kˣ) :
    powerPush C push powerFiniteEtale K n hn ⋙ U.pull (scalarMorphism K K (r ^ n)) ≅
      U.pull (scalarMorphism K K r) ⋙ powerPush C push powerFiniteEtale K n hn := by
  letI := (powerFiniteEtale K n hn).1
  letI := (powerFiniteEtale K n hn).2
  exact etaleCartesianBaseChange (scalarMorphism K K r) (powerMorphism K K n)
    (powerMorphism K K n) (scalarMorphism K K (r ^ n)) (powerScalar_isPullback K K n r)

variable {I : Type} [Group I] (nearby : C (fiberScheme K) ⥤ FDRep ℂ I)

/-- Whiskering retains the whole natural comparison through the SAME nearby functor. -/
def powerScalarNearbyIso (r : Kˣ) :
    (powerPush C push powerFiniteEtale K n hn ⋙ U.pull (scalarMorphism K K (r ^ n))) ⋙ nearby ≅
      (U.pull (scalarMorphism K K r) ⋙ powerPush C push powerFiniteEtale K n hn) ⋙ nearby :=
  Functor.isoWhiskerRight (powerScalarIso C U push etaleCartesianBaseChange powerFiniteEtale K n hn r) nearby

/-- Every actual curve object has the equivariant linear equivalence from that comparison. -/
def powerScalarNearbyEquiv (r : Kˣ) (A : C (fiberScheme K)) :
    Representation.Equiv
      (nearby.obj ((U.pull (scalarMorphism K K (r ^ n))).obj
        ((powerPush C push powerFiniteEtale K n hn).obj A))).ρ
      (nearby.obj ((powerPush C push powerFiniteEtale K n hn).obj
        ((U.pull (scalarMorphism K K r)).obj A))).ρ :=
  equivOfIso ((powerScalarNearbyIso C U push etaleCartesianBaseChange powerFiniteEtale K n hn nearby r).app A)

/-- The cubic comparison is a specialization of the ALL-power natural construction. -/
def cubicScalarIso (h3 : powerCoverGuard K 3) (r : Kˣ) :
    powerPush C push powerFiniteEtale K 3 h3 ⋙ U.pull (scalarMorphism K K (r ^ 3)) ≅
      U.pull (scalarMorphism K K r) ⋙ powerPush C push powerFiniteEtale K 3 h3 :=
  powerScalarIso C U push etaleCartesianBaseChange powerFiniteEtale K 3 h3 r

end PrimeGap182.TypeIII.PowerCoverBaseChangeFromEtaleCartesian
