import TypeIIIArithmeticBoundaryFromSources

/-!
# Source-derived boundary data for the actual cohomological realization

Retain the original boundary space, injection and Frobenius. The general
boundary sequence supplies exactness, and source arithmetic naturality
supplies the Jordan-centralizer comparison required by the posted
CohomologicalRealization. No completed family boundary model is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace PrimeGap182.TypeIII.BoundaryCohomologyFromSources

open PublishedPhysicalConstruction PublishedMackey PublishedPhaseApplication
open RegularUnipotentBoundary BoundaryFromSourceModels RestrictionFrobenius
open ArithmeticBoundaryFromSources FrobeniusBoundaryBasis

universe u v w z a b
variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{w} ℂ} {S : BoundarySequence D H F}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F S)
  (P : ArithmeticRestriction Z) (Fr : F ⟶ F)
  (B : ArithmeticBoundary Z P Fr)

/-- The SAME general boundary objects, maps and action. -/
def boundaryData : BoundaryCohomologyData H F where
  space := S.space
  toCompact := S.toCompact
  frobenius := B.boundaryFr

omit [Abelian C] in
/-- Exactness and arithmetic compatibility follow from the general
sequence and boundary naturality. Both interfaces retain the tame-zero
condition for exactness in relative ordinary cohomology. -/
theorem boundaryRules : BoundaryCohomologyRules D H F Fr (boundaryData Z P Fr B) where
  injective := S.injective
  exact := S.exact
  frobenius A := by
    apply LinearMap.ext
    exact B.toCompact_natural A

variable (K : KloostermanInputData D) (R : CurveRules D)
  {rho : Representation ℂ G0 ((Fin 3 → ℂ))} (regular : RegularModel rho)
  (hfirst : Representation.Equiv (Z.zero K.first).ρ rho)
  (hsecond : Representation.Equiv (Z.zero K.second).ρ rho)
  (hadditive : Representation.Equiv (Z.zero K.additive).ρ (Representation.trivial ℂ G0 ℂ))
  (tfirst tsecond : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
  (hf : ∀ x, hfirst (P.zeroFr K.first x) = tfirst (hfirst x))
  (hs : ∀ x, hsecond (P.zeroFr K.second x) = tsecond (hsecond x))
  (ha : ∀ x, hadditive (P.zeroFr K.additive x) = hadditive x)
  (q c : ℂ) (hq : q ≠ 0) (hc : c ≠ 0)
  (hnf : LinearMap.toMatrix' tfirst.toLinearMap * jordanThree ℂ =
    q⁻¹ • (jordanThree ℂ * LinearMap.toMatrix' tfirst.toLinearMap))
  (hns : LinearMap.toMatrix' tsecond.toLinearMap * jordanThree ℂ =
    q⁻¹ • (jordanThree ℂ * LinearMap.toMatrix' tsecond.toLinearMap))
  (hlf : LinearMap.toMatrix' tfirst.toLinearMap 0 0 = c)
  (hls : LinearMap.toMatrix' tsecond.toLinearMap 0 0 = c)
  (h1 : 1 - q⁻¹ ≠ 0) (h2 : 1 - q⁻¹ ^ 2 ≠ 0)

local notation "a₁" => ((LinearMap.toMatrix' tfirst.toLinearMap 0 1 / c -
  LinearMap.toMatrix' tsecond.toLinearMap 0 1 / c) / q)
local notation "a₂" => ((LinearMap.toMatrix' tfirst.toLinearMap 0 2 / c +
  (LinearMap.toMatrix' tsecond.toLinearMap 0 1 / c) ^ 2 -
  LinearMap.toMatrix' tsecond.toLinearMap 0 2 / c -
  (LinearMap.toMatrix' tfirst.toLinearMap 0 1 / c) *
    (LinearMap.toMatrix' tsecond.toLinearMap 0 1 / c)) / q ^ 2)

/-- The old local-boundary record on the actual general boundary space.
Its Frobenius identity follows from the source-derived boundary model
and injectivity of the original boundary map. -/
def localBoundaryData :
    KloostermanBoundaryData D H F K (boundaryData Z P Fr B) q hq where
  identification := (centralizerBasisEquiv q a₁ a₂).trans
    (boundaryIdentification Z K R regular hfirst hsecond hadditive)
  frobenius := by
    apply LinearMap.ext
    intro X
    apply S.injective K.input (K.input_lisse R) (K.input_slope_one R)
    change S.toCompact K.input (B.boundaryFr K.input
      (boundaryIdentification Z K R regular hfirst hsecond hadditive
        (centralizerBasisEquiv q a₁ a₂ X))) = _
    rw [← B.toCompact_natural]
    exact LinearMap.congr_fun
      (originBoundaryFromSources Z P Fr K hfirst hsecond hadditive tfirst tsecond hf hs ha
        R regular B q c hq hc hnf hns hlf hls h1 h2).frobenius X

omit [Abelian C] in
/-- Inserting the new records preserves the exact boundary injection
already constructed from the sources, not only its image or trace. -/
theorem originBoundary_preserves_map :
    (originBoundaryModel K R (boundaryData Z P Fr B) (boundaryRules Z P Fr B) q hq
      (localBoundaryData Z P Fr B K R regular hfirst hsecond hadditive tfirst tsecond
        hf hs ha q c hq hc hnf hns hlf hls h1 h2)).boundary =
    (originBoundaryFromSources Z P Fr K hfirst hsecond hadditive tfirst tsecond hf hs ha
      R regular B q c hq hc hnf hns hlf hls h1 h2).boundary := rfl

end PrimeGap182.TypeIII.BoundaryCohomologyFromSources

#print axioms PrimeGap182.TypeIII.BoundaryCohomologyFromSources.boundaryData
#print axioms PrimeGap182.TypeIII.BoundaryCohomologyFromSources.boundaryRules
#print axioms PrimeGap182.TypeIII.BoundaryCohomologyFromSources.localBoundaryData
#print axioms PrimeGap182.TypeIII.BoundaryCohomologyFromSources.originBoundary_preserves_map
