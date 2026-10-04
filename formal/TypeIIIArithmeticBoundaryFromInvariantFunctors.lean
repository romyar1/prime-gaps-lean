import TypeIIIGeometricBoundaryFromFunctors
import TypeIIIArithmeticBoundaryFromSources
import TypeIIIArithmeticCovarianceFromSpecialization

/-!
# Arithmetic boundary on the actual invariant product

Frobenius conjugates inertia; it need not commute with it. In finite
dimension, this covariance suffices for an invertible Frobenius to
preserve invariant vectors, even without a surjectivity premise on the
inertia endomorphism. The boundary action is the product of these induced
actions on the same zero and infinity functors used by localization.

General infinity covariance and equivariance of the original connecting
map remain published inputs. No boundary action or zero-projection
compatibility is supplied separately.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors

open PublishedPhysicalConstruction BoundaryFromSourceModels RestrictionFrobenius
open ArithmeticBoundaryFromSources GeometricBoundaryFromFunctors

universe u v a b c d

section Invariants
variable {G : Type a} [Group G] (V : FDRep ℂ G)
  (Fr : V.V ≃ₗ[ℂ] V.V) (phi : G →* G)
  (cov : ∀ g x, Fr (V.ρ g x) = V.ρ (phi g) (Fr x))

include cov in
theorem inverse_preserves_invariants (x : Representation.invariants V.ρ) :
    Fr.symm x.val ∈ Representation.invariants V.ρ := by
  intro g
  apply Fr.injective
  rw [cov, Fr.apply_symm_apply]
  exact x.property (phi g)

def inverseOnInvariants : Representation.invariants V.ρ →ₗ[ℂ] Representation.invariants V.ρ where
  toFun x := ⟨Fr.symm x.val, inverse_preserves_invariants V Fr phi cov x⟩
  map_add' x y := by apply Subtype.ext; exact Fr.symm.map_add _ _
  map_smul' s x := by apply Subtype.ext; exact Fr.symm.map_smul s _

include cov in
/-- The inverse restricts injectively to the finite-dimensional invariant
space, hence surjectively. Its inverse therefore preserves that space too. -/
theorem preserves_invariants (x : Representation.invariants V.ρ) :
    Fr x.val ∈ Representation.invariants V.ρ := by
  let f := inverseOnInvariants V Fr phi cov
  have hi : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    apply Fr.symm.injective
    exact congrArg Subtype.val h
  have hs : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hi
  obtain ⟨y, hy⟩ := hs x
  have hv : Fr x.val = y.val := by
    have h := congrArg Subtype.val hy
    change Fr.symm y.val = x.val at h
    rw [← h, Fr.apply_symm_apply]
  rw [hv]
  exact y.property

def invariantAction : Representation.invariants V.ρ ≃ₗ[ℂ] Representation.invariants V.ρ where
  toFun x := ⟨Fr x.val, preserves_invariants V Fr phi cov x⟩
  invFun x := ⟨Fr.symm x.val, inverse_preserves_invariants V Fr phi cov x⟩
  left_inv x := by apply Subtype.ext; exact Fr.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact Fr.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact Fr.map_add _ _
  map_smul' s x := by apply Subtype.ext; exact Fr.map_smul s _

end Invariants

variable {Input : Type u} [Category.{c} Input] [MonoidalCategory Input]
  {Point : Type v} {C : Type} [Category.{d} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat ℂ} {dualInput : Inputᵒᵖ ⥤ Input}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (S : Data (G0 := G0) (Ginf := Ginf) D H F dualInput)
  (tensorComparison : ∀ A B, D.tensor A B ≅ A ⊗ B)
  (dualComparison : ∀ A, D.dual A ≅ dualInput.obj (Opposite.op A))
  (P : ArithmeticRestriction (S.restriction tensorComparison dualComparison))
  (Fr : F ⟶ F) (phi : G0 →* G0)
  (cov : ∀ A g x, P.zeroFr A ((S.zero.obj A).ρ g x) =
    (S.zero.obj A).ρ (phi g) (P.zeroFr A x))

/-- General local infinity action and equivariance of the original
localization connecting map, on the literal invariant product. The zero
action is the existing original-input action; its covariance is supplied
by the same arithmetic specialization used for source normalization. -/
structure Inputs where
  infinityFr : ∀ A, (S.infinity.obj A).V ≃ₗ[ℂ] (S.infinity.obj A).V
  infinityConjugation : Ginf →* Ginf
  infinityCovariance : ∀ A g x, infinityFr A ((S.infinity.obj A).ρ g x) =
    (S.infinity.obj A).ρ (infinityConjugation g) (infinityFr A x)
  connectingNatural : ∀ A x y,
    (Fr.app (H.compact A)).hom (S.toCompact A (x,y)) =
      S.toCompact A
        (invariantAction (S.zero.obj A) (P.zeroFr A) phi (cov A) x,
         invariantAction (S.infinity.obj A) (infinityFr A) infinityConjugation
           (infinityCovariance A) y)

variable {S tensorComparison dualComparison P Fr phi cov}
  (W : Inputs S tensorComparison dualComparison P Fr phi cov)

/-- The action on the complete boundary is the product of the two
restricted Frobenius actions; no separate boundary operator is chosen. -/
def Inputs.boundaryAction (A : Input) : Module.End ℂ (S.boundarySequence.space A) :=
  (invariantAction (S.zero.obj A) (P.zeroFr A) phi (cov A)).toLinearMap.prodMap
    (invariantAction (S.infinity.obj A) (W.infinityFr A) W.infinityConjugation
      (W.infinityCovariance A)).toLinearMap

/-- Both original arithmetic boundary laws follow on these exact maps.
The zero projection law is definitional, and connecting-map compatibility
is the general localization law on the same invariant product. -/
def Inputs.arithmeticBoundary :
    ArithmeticBoundary (S.restriction tensorComparison dualComparison) P Fr where
  boundaryFr := W.boundaryAction
  toCompact_natural A x := W.connectingNatural A x.1 x.2
  zero_natural _ _ _ := rfl

end PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors

#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors.inverse_preserves_invariants
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors.preserves_invariants
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors.invariantAction
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors.Inputs.boundaryAction
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromInvariantFunctors.Inputs.arithmeticBoundary
