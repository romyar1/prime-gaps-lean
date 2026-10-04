import TypeIIINativeSurfaceFromGeometricStalks
import TypeIIILinearRadialPhaseFromPoleTransport

/-!
# Support invariance from the same geometric dimensions

Native support is defined by the union of its nonzero ordinary stalk
dimensions. The existing coefficient-transport dimension invariance
therefore implies support invariance. The support-definition equality is
reflexivity in the native root and is not an additional geometric premise.
The other eight original local laws keep their exact scope.
-/

noncomputable section
open scoped Classical

namespace PrimeGap182.TypeIII.NativeLocalSupportFromGeometricDimensions
open PublishedSupportRules PublishedFourierRules

universe v w
variable {k : Type} [Field k] {Obj : Type v} {CurveObj : Type w}
  (S : SurfaceData k Obj) (C : CoefficientTransport S)
  (F : FourierData k Obj CurveObj)

/-- Only the eight OTHER scoped local laws. -/
structure RemainingLocalRules : Prop where
  profile_isomorphic : ∀ {P Q : Obj}, C.Isomorphic P Q →
    (F.HasSimpleRadialPhases P ↔ F.HasSimpleRadialPhases Q)
  phases_isomorphic : ∀ {P Q : Obj}, C.Isomorphic P Q → F.phases P = F.phases Q
  inverse_constituent : ∀ P Q, Q ∈ S.constituents (F.fourier P) →
    ∃ P0 ∈ S.constituents P, C.Isomorphic (F.inverse Q) P0
  profile_constituent : ∀ P P0, F.HasSimpleRadialPhases P →
    P0 ∈ S.constituents P → F.HasSimpleRadialPhases P0
  phases_constituent : ∀ P P0, F.HasSimpleRadialPhases P →
    P0 ∈ S.constituents P → F.phases P0 ⊆ F.phases P
  phases_nonempty : ∀ P, F.HasSimpleRadialPhases P →
    S.support P = Set.univ → (F.phases P).Nonempty
  inverse_point_zero_phase : ∀ Q, S.Simple Q → ∀ z : k × k,
    S.support Q = {z} → (0 : AlgebraicClosure (RatFunc k)) ∈ F.phases (F.inverse Q)
  inverse_line_pullback : ∀ Q, S.Simple Q → ∀ a b : k,
    (a ≠ 0 ∨ b ≠ 0) → S.support Q ⊆ ScalingLines.originLine a b →
    ∃ X : CurveObj, C.Isomorphic (F.inverse Q) (F.linearPullback (b, -a) X)

variable (supportDefinition : ∀ P, S.support P = {z | ∃ i : Fin 3, S.geomDim P z i ≠ 0})

include supportDefinition in
/-- Existing dimension invariance suffices on every object and point. -/
theorem support_isomorphic {P Q : Obj} (h : C.Isomorphic P Q) :
    S.support P = S.support Q := by
  rw [supportDefinition P, supportDefinition Q]
  ext z
  change (∃ i : Fin 3, S.geomDim P z i ≠ 0) ↔ (∃ i : Fin 3, S.geomDim Q z i ≠ 0)
  simp_rw [C.geomDim_isomorphic h z]

include supportDefinition in
/-- Construct the original nine-field OtherLocalRules. -/
theorem RemainingLocalRules.otherLocalRules (R : RemainingLocalRules S C F) :
    LinearRadialPhaseFromPoleTransport.OtherLocalRules (F := F) S C where
  support_isomorphic := support_isomorphic S C supportDefinition
  profile_isomorphic := R.profile_isomorphic
  phases_isomorphic := R.phases_isomorphic
  inverse_constituent := R.inverse_constituent
  profile_constituent := R.profile_constituent
  phases_constituent := R.phases_constituent
  phases_nonempty := R.phases_nonempty
  inverse_point_zero_phase := R.inverse_point_zero_phase
  inverse_line_pullback := R.inverse_line_pullback

end PrimeGap182.TypeIII.NativeLocalSupportFromGeometricDimensions

#print axioms PrimeGap182.TypeIII.NativeLocalSupportFromGeometricDimensions.support_isomorphic
#print axioms PrimeGap182.TypeIII.NativeLocalSupportFromGeometricDimensions.RemainingLocalRules.otherLocalRules
