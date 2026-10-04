import TypeIIIConstantSignInertia
import TypeIIIGenericPhysicalEntry
import TypeIIIFourierStalkInertia

/-!
# The actual physical entry restricts to its unsigned parabolic core

Use inverse-image composition on the proved radial/physical scheme map,
then remove the constant sign by its derived geometric-inertia action.
The original physical entry and its original parabolic core are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.PhysicalUnsignedInertia

open PublishedPhysicalConstruction GenericCurvePullback GenericPhysicalEntry
open PhysicalTorusMorphism ConstantSignInertia TensorListRepresentation

universe u v w z a b c d e
variable {p : ℕ} [Fact p.Prime]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  {C' : Type w} [Category.{z} C'] [MonoidalCategory C']
  {Input : Type a} {Point : Type b} {D : CurveData Input Point}
  {H : CohomologyData Input C} {P : ParameterData C}
  {E : Type c} [Field E] {G : Type d} [Group G]
  {W : Type e} [Group W]
  (O : TorusOperationData p C)
  (B : (parameterScheme (ZMod p) ⟶ torusScheme (ZMod p)) → C ⥤ C')
  (PC : BasePullbackComposition O B)
  [∀ f, (B f).Monoidal]
  (J : C' ⥤ FDRep E G) [J.Monoidal]
  (S : SignTensorData P)
  (degree : W →* Multiplicative ℤ) (inertia : G →* W)
  (geometric : ∀ g, degree (inertia g) = 1)
  (RS : ∀ f, SignLineModel degree inertia ((B f ⋙ J).obj S.line))

/-- The same physical entry and same generic radial pullback used by
the original tensor construction. Its arithmetic sign is removed only
in the geometric-inertia representation. -/
def physicalUnsignedInertiaEquiv (A : KloostermanInputData D) (alpha m n : (ZMod p)ˣ) :
    Representation.Equiv
      ((B (genericRadialMorphism (ZMod p)) ⋙ J).obj
        (pulledEntry (H := H) (P := P) A O alpha m n)).ρ
      ((B (radialParameterMorphism (ZMod p) alpha m n) ⋙ J).obj
        (parabolicCore H A.input)).ρ :=
  (equivOfIso (J.mapIso (genericPhysicalEntryIso O B PC A alpha m n))).trans
    (signedInertiaEquiv degree inertia geometric P S
      (B (radialParameterMorphism (ZMod p) alpha m n) ⋙ J)
      (RS (radialParameterMorphism (ZMod p) alpha m n)) (parabolicCore H A.input))

end PrimeGap182.TypeIII.PhysicalUnsignedInertia

#print axioms PrimeGap182.TypeIII.PhysicalUnsignedInertia.physicalUnsignedInertiaEquiv
