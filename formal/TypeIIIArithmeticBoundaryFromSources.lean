import TypeIIIRestrictionFrobenius
import TypeIIIFrobeniusBoundaryBasis

/-!
# Arithmetic boundary from individual source models and general naturality

The boundary injection is the same one constructed from inertia invariants.
Its Frobenius compatibility is derived by composing the general restriction
and boundary naturality laws with the individual source Frobenius models.
The resulting original `OriginBoundaryModel` does not assume a completed
family boundary action or a naturality square for the finished tensor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical TensorProduct

namespace PrimeGap182.TypeIII.ArithmeticBoundaryFromSources

open CategoryTheory PublishedPhysicalConstruction PublishedMackey PublishedPhaseApplication
open RegularUnipotentBoundary BoundaryFromSourceModels RestrictionFrobenius
open TensorBoundaryFrobenius BoundaryFrobeniusNormalization FrobeniusBoundaryBasis

/-- Matrix inversion agrees with the inverse of the actual source
automorphism; invertibility is supplied by that automorphism itself. -/
theorem matrix_inverse_of_equiv {k : Type*} [Field k]
    (e : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) :
    (LinearMap.toMatrix' e.toLinearMap)⁻¹ = LinearMap.toMatrix' e.symm.toLinearMap := by
  apply Matrix.inv_eq_right_inv
  rw [← LinearMap.toMatrix'_comp]
  have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x
  rw [h, LinearMap.toMatrix'_id]

universe u v w z a b
variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{w} ℂ} {S : BoundarySequence D H F}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F S)
  (P : ArithmeticRestriction Z) (Fr : F ⟶ F)

/-- General naturality for the boundary sequence and its zero-inertia
projection, for every lisse input. No Kloosterman recipe appears here. -/
structure ArithmeticBoundary where
  boundaryFr : ∀ A, Module.End ℂ (S.space A)
  toCompact_natural : ∀ A x,
    (Fr.app (H.compact A)).hom (S.toCompact A x) =
      S.toCompact A (boundaryFr A x)
  zero_natural : ∀ A (h : D.Lisse A) x,
    ((Z.boundary A h (boundaryFr A x)).1).val =
      P.zeroFr A ((Z.boundary A h x).1).val

variable (K : KloostermanInputData D)
  {rho : Representation ℂ G0 (ModelSpace (k := ℂ))}
  (hfirst : Representation.Equiv (Z.zero K.first).ρ rho)
  (hsecond : Representation.Equiv (Z.zero K.second).ρ rho)
  (hadditive : Representation.Equiv (Z.zero K.additive).ρ (Representation.trivial ℂ G0 ℂ))

/-- Raw matrix coordinates on the original restricted input, through its
literal tensor/dual restriction and the three individual source models. -/
def sourceCoordinates : (Z.zero K.input).V →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ :=
  tensorMatrixEquiv.toLinearMap.comp
    ((sourceTensorEquiv (Z.zero K.first) (Z.zero K.second) (Z.zero K.additive)
      hfirst hsecond hadditive).toLinearMap.comp (zeroInputEquiv Z K).toLinearMap)

variable (tfirst tsecond : ModelSpace (k := ℂ) ≃ₗ[ℂ] ModelSpace (k := ℂ))
  (hf : ∀ x, hfirst (P.zeroFr K.first x) = tfirst (hfirst x))
  (hs : ∀ x, hsecond (P.zeroFr K.second x) = tsecond (hsecond x))
  (ha : ∀ x, hadditive (P.zeroFr K.additive x) = hadditive x)

include hf hs ha in
omit [Abelian C] in
/-- Derive the relative source action on the actual restricted input.
Only the three individual source Frobenius comparisons are premises. -/
theorem sourceCoordinates_natural (x : (Z.zero K.input).V) :
    sourceCoordinates Z K hfirst hsecond hadditive (P.zeroFr K.input x) =
      LinearMap.toMatrix' tfirst.toLinearMap * sourceCoordinates Z K hfirst hsecond hadditive x *
        (LinearMap.toMatrix' tsecond.toLinearMap)⁻¹ := by
  change tensorMatrixEquiv (sourceTensorEquiv _ _ _ hfirst hsecond hadditive
    (zeroInputEquiv Z K (P.zeroFr K.input x))) = _
  rw [zeroInputEquiv_natural Z P K,
    sourceTensorEquiv_natural _ _ _ hfirst hsecond hadditive
      (P.zeroFr K.first) (P.zeroFr K.second) (P.zeroFr K.additive).toLinearMap
      tfirst tsecond hf hs ha]
  rw [matrix_inverse_of_equiv]
  have hcoords : sourceCoordinates Z K hfirst hsecond hadditive x =
      tensorMatrixEquiv (sourceTensorEquiv _ _ _ hfirst hsecond hadditive (zeroInputEquiv Z K x)) := rfl
  rw [hcoords]
  simpa only [Matrix.toLin'_toMatrix'] using
    tensorMatrixEquiv_natural (LinearMap.toMatrix' tfirst.toLinearMap)
      (LinearMap.toMatrix' tsecond.symm.toLinearMap)
      (sourceTensorEquiv _ _ _ hfirst hsecond hadditive (zeroInputEquiv Z K x))

variable (R : CurveRules D) (M : RegularModel rho)

omit [Abelian C] in
/-- These are exactly the coordinates of the existing geometric boundary
comparison, including removal of the positive-slope infinity summand. -/
theorem boundaryIdentification_coordinates (x : S.space K.input) :
    ((boundaryIdentification Z K R M hfirst hsecond hadditive).symm x).val =
      sourceCoordinates Z K hfirst hsecond hadditive
        ((Z.boundary K.input (K.input_lisse R) x).1).val := rfl

variable (B : ArithmeticBoundary Z P Fr)
  (q c : ℂ) (hq : q ≠ 0) (hc : c ≠ 0)
  (hnf : LinearMap.toMatrix' tfirst.toLinearMap * jordanThree ℂ =
    q⁻¹ • (jordanThree ℂ * LinearMap.toMatrix' tfirst.toLinearMap))
  (hns : LinearMap.toMatrix' tsecond.toLinearMap * jordanThree ℂ =
    q⁻¹ • (jordanThree ℂ * LinearMap.toMatrix' tsecond.toLinearMap))
  (hlf : LinearMap.toMatrix' tfirst.toLinearMap 0 0 = c)
  (hls : LinearMap.toMatrix' tsecond.toLinearMap 0 0 = c)

include hf hs ha hq hc hnf hns hlf hls in
omit [Abelian C] in
/-- Naturality of the original full boundary identification is a
conclusion of general laws and single-source models. -/
theorem boundaryIdentification_natural (X : jordanThreeCentralizer ℂ) :
    B.boundaryFr K.input (boundaryIdentification Z K R M hfirst hsecond hadditive X) =
      boundaryIdentification Z K R M hfirst hsecond hadditive
        (relativeOperator q c (LinearMap.toMatrix' tfirst.toLinearMap)
          (LinearMap.toMatrix' tsecond.toLinearMap) X) := by
  apply (boundaryIdentification Z K R M hfirst hsecond hadditive).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [boundaryIdentification_coordinates, B.zero_natural,
    sourceCoordinates_natural Z P K hfirst hsecond hadditive tfirst tsecond hf hs ha,
    relativeOperator_val q c hq hc _ _ hnf hns hlf hls]
  have h := boundaryIdentification_coordinates Z K hfirst hsecond hadditive R M
    (boundaryIdentification Z K R M hfirst hsecond hadditive X)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h]

include B hf hs ha hq hc hnf hns hlf hls in
omit [Abelian C] in
/-- Carry the derived relative action through the actual boundary
injection into the original compact cohomology. -/
theorem geometricBoundaryModel_frobenius :
    (Fr.app (H.compact K.input)).hom.comp
        (geometricBoundaryModel Z K R M hfirst hsecond hadditive).boundary =
      (geometricBoundaryModel Z K R M hfirst hsecond hadditive).boundary.comp
        (relativeOperator q c (LinearMap.toMatrix' tfirst.toLinearMap)
          (LinearMap.toMatrix' tsecond.toLinearMap)) := by
  apply LinearMap.ext
  intro X
  change (Fr.app (H.compact K.input)).hom
    (S.toCompact K.input (boundaryIdentification Z K R M hfirst hsecond hadditive X)) = _
  rw [B.toCompact_natural,
    boundaryIdentification_natural Z P Fr K hfirst hsecond hadditive
      tfirst tsecond hf hs ha R M B q c hq hc hnf hns hlf hls]
  rfl

/-- Construct the unchanged arithmetic boundary interface, with its
Frobenius square proved from the individual sources and general laws. -/
def originBoundaryFromSources (h1 : 1 - q⁻¹ ≠ 0) (h2 : 1 - q⁻¹ ^ 2 ≠ 0) :
    OriginBoundaryModel H F K.input Fr q hq :=
  originBoundaryOfRelativeAction H F Fr K.input
    (geometricBoundaryModel Z K R M hfirst hsecond hadditive) q
    ((LinearMap.toMatrix' tfirst.toLinearMap 0 1 / c -
      LinearMap.toMatrix' tsecond.toLinearMap 0 1 / c) / q)
    ((LinearMap.toMatrix' tfirst.toLinearMap 0 2 / c +
      (LinearMap.toMatrix' tsecond.toLinearMap 0 1 / c) ^ 2 -
      LinearMap.toMatrix' tsecond.toLinearMap 0 2 / c -
      (LinearMap.toMatrix' tfirst.toLinearMap 0 1 / c) *
        (LinearMap.toMatrix' tsecond.toLinearMap 0 1 / c)) / q ^ 2)
    hq h1 h2
    (geometricBoundaryModel_frobenius Z P Fr K hfirst hsecond hadditive
      tfirst tsecond hf hs ha R M B q c hq hc hnf hns hlf hls)

end PrimeGap182.TypeIII.ArithmeticBoundaryFromSources

#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.matrix_inverse_of_equiv
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.sourceCoordinates
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.sourceCoordinates_natural
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.boundaryIdentification_coordinates
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.boundaryIdentification_natural
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.geometricBoundaryModel_frobenius
#print axioms PrimeGap182.TypeIII.ArithmeticBoundaryFromSources.originBoundaryFromSources
