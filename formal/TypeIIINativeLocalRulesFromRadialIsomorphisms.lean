import TypeIIINativeCoefficientTransportFromIsomorphisms
import TypeIIIPhaseRulesFromSeparatedCharacters
import TypeIIINativeTheoryFromRadialPhaseData
import TypeIIIConstantFieldLocalData

/-!
# Native local invariance from the same radial functor and characters

Native isomorphisms map through the SAME actual radial inverse-image/H^-2
functor. The ten algebraic phase rules for canonicalPD B J as, transported
through the original phaseData coordinate change, derive profile/phase
isomorphism invariance. Support invariance is already derived from actual
geometric dimensions. Only the other six scoped local rules remain.
No completed coefficient/local/phase record or invariance premise is input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.NativeLocalRulesFromRadialIsomorphisms
open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages NativeSurfaceFromGeometricStalks
open NativeCoefficientTransportFromIsomorphisms PublishedSupportRules PublishedFourierRules
open PublishedPhaseApplication PhaseDataFromOriginalCharacters OriginPoleWildFromOriginalParameter

universe mu g
variable {p : ℕ} [Fact p.Prime] {J : Type}
  {B : SourceInverseImageSystem.System.{0,mu} (ZMod p)}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{mu} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{mu} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{mu} (OC i)] [∀ i, Abelian (OC i)]
  {A : OrdinarySystem (extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme))
    (extensionObjects B (extraObjects NC LC OC))}

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{mu} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

variable (D : Admissibility A) (point : J)
  (hPoint : otherScheme point = pointScheme (AlgebraicClosure (ZMod p)))
  (fiber : OC point ⥤ ModuleCat.{mu} ℂ) (O : RemainingObservables D)
  (coefficientOp : Obj D → Obj D)
  (dilateOp : (AlgebraicClosure (ZMod p))ˣ → Obj D → Obj D)
  (L : RemainingTransportLaws D point hPoint fiber O coefficientOp dilateOp)
  (smooth : SmoothPullbackLaw D) (fourierOp inverseOp : Obj D → Obj D)
  {G : Type g} [Group G] (W : OrdinaryWild (E := ℂ) (G := G) A)
  (JRep : B.Obj .parameter ⥤ FDRep ℂ G) (as : B.Obj .line)

/-- The exact original canonical phase data, with the original algebraic
constant-field coordinate change. No new PhaseData is selected. -/
abbrev rebasedPhaseData : PhaseData (AlgebraicClosure (ZMod p)) ℂ G :=
  ConstantFieldLocalData.phaseData (ZMod p) (AlgebraicClosure (ZMod p)) (canonicalPD B JRep as)

abbrev nativeOperations : Operations D :=
  NativeTheoryFromRadialPhaseData.operations D fourierOp inverseOp W (rebasedPhaseData JRep as)

abbrev nativeFourierData : FourierData (AlgebraicClosure (ZMod p)) (Obj D) (CurveObj D) :=
  fourierData smooth (nativeOperations D fourierOp inverseOp W JRep as)

variable
  (characters : CharacterLaws (oldCharacter (J := JRep) as))
  (characterOperations : PhaseRulesFromSeparatedCharacters.CharacterOperations (oldCharacter (J := JRep) as))

include characters characterOperations in
/-- Actual native Iso maps through actual radial inverse image/H^-2/W;
canonicalPhaseRules.transport and original phaseData derive both invariances. -/
theorem radialTransport {P Q : Obj D} (h : Nonempty (P ≅ Q)) :
    ((rebasedPhaseData JRep as).HasProfile (radial (D := D) W P) ↔
      (rebasedPhaseData JRep as).HasProfile (radial (D := D) W Q)) ∧
    (rebasedPhaseData JRep as).phases (radial (D := D) W P) =
      (rebasedPhaseData JRep as).phases (radial (D := D) W Q) := by
  let e := TensorListRepresentation.equivOfIso ((radialFunctor (D := D) W).mapIso (Classical.choice h))
  exact (ConstantFieldLocalData.phaseRules (ZMod p) (AlgebraicClosure (ZMod p))
    (canonicalPD B JRep as)
    (PhaseRulesFromSeparatedCharacters.canonicalPhaseRules B JRep as characters characterOperations)).transport
      _ _ e.toIntertwiningMap e.toLinearEquiv.bijective

/-- The OTHER six original local fields, with their full original guards.
Their isomorphism conclusions now mean actual native categorical Iso. -/
structure RemainingLocalRules : Prop where
  inverse_constituent : ∀ P Q,
    Q ∈ (surfaceData D point hPoint fiber O).constituents
      ((nativeFourierData D smooth fourierOp inverseOp W JRep as).fourier P) →
    ∃ P0 ∈ (surfaceData D point hPoint fiber O).constituents P,
      L.transport.Isomorphic ((nativeFourierData D smooth fourierOp inverseOp W JRep as).inverse Q) P0
  profile_constituent : ∀ P P0,
    (nativeFourierData D smooth fourierOp inverseOp W JRep as).HasSimpleRadialPhases P →
    P0 ∈ (surfaceData D point hPoint fiber O).constituents P →
    (nativeFourierData D smooth fourierOp inverseOp W JRep as).HasSimpleRadialPhases P0
  phases_constituent : ∀ P P0,
    (nativeFourierData D smooth fourierOp inverseOp W JRep as).HasSimpleRadialPhases P →
    P0 ∈ (surfaceData D point hPoint fiber O).constituents P →
    (nativeFourierData D smooth fourierOp inverseOp W JRep as).phases P0 ⊆
      (nativeFourierData D smooth fourierOp inverseOp W JRep as).phases P
  phases_nonempty : ∀ P,
    (nativeFourierData D smooth fourierOp inverseOp W JRep as).HasSimpleRadialPhases P →
    (surfaceData D point hPoint fiber O).support P = Set.univ →
    ((nativeFourierData D smooth fourierOp inverseOp W JRep as).phases P).Nonempty
  inverse_point_zero_phase : ∀ Q, (surfaceData D point hPoint fiber O).Simple Q →
    ∀ z : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p),
    (surfaceData D point hPoint fiber O).support Q = {z} →
    (0 : AlgebraicClosure (RatFunc (AlgebraicClosure (ZMod p)))) ∈
      (nativeFourierData D smooth fourierOp inverseOp W JRep as).phases
        ((nativeFourierData D smooth fourierOp inverseOp W JRep as).inverse Q)
  inverse_line_pullback : ∀ Q, (surfaceData D point hPoint fiber O).Simple Q →
    ∀ a b : AlgebraicClosure (ZMod p), (a ≠ 0 ∨ b ≠ 0) →
    (surfaceData D point hPoint fiber O).support Q ⊆ ScalingLines.originLine a b →
    ∃ X : CurveObj D, L.transport.Isomorphic
      ((nativeFourierData D smooth fourierOp inverseOp W JRep as).inverse Q)
      ((nativeFourierData D smooth fourierOp inverseOp W JRep as).linearPullback (b, -a) X)

variable {D point hPoint fiber O coefficientOp dilateOp L smooth fourierOp inverseOp W JRep as}
  (R : RemainingLocalRules D point hPoint fiber O coefficientOp dilateOp L smooth fourierOp inverseOp W JRep as)

include characters characterOperations R in
/-- Construct original OtherLocalRules9: support/profile/phases invariance
are derived, while the other six explicit geometric laws are preserved. -/
theorem RemainingLocalRules.otherLocalRules : LinearRadialPhaseFromPoleTransport.OtherLocalRules
    (F := nativeFourierData D smooth fourierOp inverseOp W JRep as)
    (surfaceData D point hPoint fiber O) L.transport where
  support_isomorphic := NativeLocalSupportFromGeometricDimensions.support_isomorphic
    (surfaceData D point hPoint fiber O) L.transport (fun _ => rfl)
  profile_isomorphic h := (radialTransport D W JRep as characters characterOperations h).1
  phases_isomorphic h := (radialTransport D W JRep as characters characterOperations h).2
  inverse_constituent := R.inverse_constituent
  profile_constituent := R.profile_constituent
  phases_constituent := R.phases_constituent
  phases_nonempty := R.phases_nonempty
  inverse_point_zero_phase := R.inverse_point_zero_phase
  inverse_line_pullback := R.inverse_line_pullback

end PrimeGap182.TypeIII.NativeLocalRulesFromRadialIsomorphisms

#print axioms PrimeGap182.TypeIII.NativeLocalRulesFromRadialIsomorphisms.radialTransport
#print axioms PrimeGap182.TypeIII.NativeLocalRulesFromRadialIsomorphisms.RemainingLocalRules.otherLocalRules
