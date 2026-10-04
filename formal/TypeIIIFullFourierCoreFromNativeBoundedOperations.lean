import TypeIIIMiddleInfinityFromActualOrdinaryOpenAndPerverseCohomology
import TypeIIIBoundedCompactRealizationFromSameOperations
import TypeIIICanonicalAffineCoefficientChange
import TypeIIIFourierOriginFromASKernel

/-!
The full Fourier core is computed on the native affine line and affine plane.
Both source x=0 and target y=0 remain in these schemes. All ambient categories
are the SAME standard bounded derived categories; the output is the SAME
universal perverse heart. No representation-to-global-sheaf functor or
henselian cycle model is constructed.

Compact pushforward is provided ONLY at the actual target projection. One
universal Nagata geometry family covers separated finite-type maps over a
field with two invertible. The existing guarded compact operations act on its
actual open/proper factorization. No functor is fabricated for invalid maps,
and the old unguarded ALL-map Fourier Data record is not silently filled.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open QSTAdmissibilityFromBoundedDerived QSTBoundedTensorFromUniversalDerivedMonoidal

universe mu
variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- Native polynomial structure map on the entire affine n-space. -/
def affineStructure (n : ℕ) : CanonicalAffineCoefficientChange.affine E n ⟶ Spec (.of E) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : E →+* MvPolynomial (Fin n) E))

instance affineStructure_locallyFiniteType (n : ℕ) :
    LocallyOfFiniteType (affineStructure E n) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap E (MvPolynomial (Fin n) E))))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The actual full affine presentation, with no coordinate inverted. -/
def affinePresentation (n : ℕ) :
    FieldPresentation E (CanonicalAffineCoefficientChange.affine E n) where
  structureMorphism := affineStructure E n
  locallyFiniteType := inferInstance
  quasiCompact := inferInstance
  separated := inferInstance

/-- The actual second projection lies over the SAME coefficient field. -/
theorem target_over : FullFourierKernelCoordinates.targetMorphism E ≫
    (affinePresentation E 1).structureMorphism =
      (affinePresentation E 2).structureMorphism := by
  dsimp only [FullFourierKernelCoordinates.targetMorphism, affinePresentation,
    affineStructure]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  simp [FullFourierKernelCoordinates.targetHom]

/-- The actual first projection has the SAME field square. -/
theorem source_over : FourierOriginFromASKernel.sourceMorphism E ≫
    (affinePresentation E 1).structureMorphism =
      (affinePresentation E 2).structureMorphism := by
  dsimp only [FourierOriginFromASKernel.sourceMorphism, affinePresentation,
    affineStructure]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  simp

/-- Positive xy commutes with the actual coefficient extension from K to E. -/
theorem kernel_coefficient_square :
    CanonicalAffineCoefficientChange.coefficientMorphism K E 2 ≫
      FullFourierKernelCoordinates.kernelMorphism K =
    FullFourierKernelCoordinates.kernelMorphism E ≫
      CanonicalAffineCoefficientChange.coefficientMorphism K E 1 := by
  dsimp only [CanonicalAffineCoefficientChange.coefficientMorphism,
    FullFourierKernelCoordinates.kernelMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [CanonicalAffineCoefficientChange.coefficientHom,
      FullFourierKernelCoordinates.kernelHom]
  · intro i
    simp [CanonicalAffineCoefficientChange.coefficientHom,
      FullFourierKernelCoordinates.kernelHom]

instance target_locallyFiniteType :
    LocallyOfFiniteType (FullFourierKernelCoordinates.targetMorphism E) := by
  have : LocallyOfFiniteType (FullFourierKernelCoordinates.targetMorphism E ≫
      (affinePresentation E 1).structureMorphism) := by
    rw [target_over]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (affinePresentation E 1).structureMorphism

/-- Every factor and every structure map uses the SAME supplied field. -/
structure CompactificationOver (E : Type) [Field E] {X Y : Scheme}
    (PX : FieldPresentation E X) (PY : FieldPresentation E Y) (f : X ⟶ Y) where
  middle : Scheme
  presentation : FieldPresentation E middle
  openMorphism : X ⟶ middle
  properMorphism : middle ⟶ Y
  [openImmersion : IsOpenImmersion openMorphism]
  [openQuasiCompact : QuasiCompact openMorphism]
  [proper : IsProper properMorphism]
  open_over : openMorphism ≫ presentation.structureMorphism = PX.structureMorphism
  proper_over : properMorphism ≫ PY.structureMorphism = presentation.structureMorphism
  factorization : openMorphism ≫ properMorphism = f

attribute [instance] CompactificationOver.openImmersion
  CompactificationOver.openQuasiCompact CompactificationOver.proper

/-- The geometry is universal before any field, object or Fourier source is selected. -/
abbrev NagataGeometry :=
  ∀ (E : Type) [Field E] (_h2 : (2 : E) ≠ 0) {X Y : Scheme}
    (PX : FieldPresentation E X) (PY : FieldPresentation E Y) (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (_over : f ≫ PY.structureMorphism = PX.structureMorphism),
    CompactificationOver E PX PY f

/-- Convert the actual same-field factorization into the existing operations' record. -/
def compactification {X Y : Scheme} (PX : FieldPresentation E X)
    (PY : FieldPresentation E Y) (f : X ⟶ Y) (h2 : (2 : E) ≠ 0)
    (c : CompactificationOver E PX PY f) : Compactification f where
  K := E
  two_ne_zero := h2
  compactified := c.middle
  source := PX
  middle := c.presentation
  target := PY
  openMorphism := c.openMorphism
  properMorphism := c.properMorphism
  open_over := c.open_over
  proper_over := c.proper_over
  factorization := c.factorization

/-- Nagata applies to the proved finite-type, separated native target projection. -/
def targetCompactification (geometry : NagataGeometry) (h2 : (2 : E) ≠ 0) :
    Compactification (FullFourierKernelCoordinates.targetMorphism E) :=
  compactification E (affinePresentation E 2) (affinePresentation E 1) _ h2
    (geometry E h2 (affinePresentation E 2) (affinePresentation E 1) _ (target_over E))

variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) := fun _ => HasDerivedCategory.standard _

/-- Actual bounded source, full plane and target, each with carrier/hom universe mu. -/
abbrev Ambient (n : ℕ) : Type mu := Bounded C (CanonicalAffineCoefficientChange.affine E n)

/-- Actual standard shift on ALL bounded objects at EVERY scheme. -/
def boundedShift (X : Scheme) (n : ℤ) : Bounded C X ⥤ Bounded C X :=
  (boundedProperty (C X)).lift ((boundedProperty (C X)).ι ⋙ shiftFunctor _ n)
    (fun A => shift_bounded (C X) A.obj A.property n)

variable (P : ∀ X : Scheme, ObjectProperty (DerivedCategory (C X)))
  (H0 : ∀ X : Scheme, DerivedCategory (C X) ⥤ (P X).FullSubcategory)
  (perverseBounded : ∀ X (A : DerivedCategory (C X)), P X A → boundedProperty (C X) A)

/-- The SAME heart inclusion, lifted into the literal bounded subcategory. -/
def heartRealization (X : Scheme) : (P X).FullSubcategory ⥤ Bounded C X :=
  (boundedProperty (C X)).lift (P X).ι (fun A => perverseBounded X A.obj A.property)

instance heartRealization_full (X : Scheme) :
    (heartRealization C P perverseBounded X).Full := by
  unfold heartRealization
  infer_instance

instance heartRealization_faithful (X : Scheme) :
    (heartRealization C P perverseBounded X).Faithful := by
  unfold heartRealization
  infer_instance

def heartRealizationFullyFaithful (X : Scheme) :
    (heartRealization C P perverseBounded X).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- SAME standard bounded inverse image for EVERY native plane-to-line map. -/
def sourcePullback (f : FullFourierKernelCoordinates.planeScheme E ⟶
    LocalFourierKernelCoordinates.affineLine E) : Ambient E C 1 ⥤ Ambient E C 2 :=
  UniversalBoundedInverseImagesFromExactSystem.pull C U f

/-- SAME ordinary AS line over K, actually extended to E and pulled to the full plane. -/
def phasePullback (f : FullFourierKernelCoordinates.planeScheme E ⟶
    LocalFourierKernelCoordinates.affineLine E) :
    C (LocalFourierKernelCoordinates.affineLine K) ⥤ Ambient E C 2 :=
  boundedDegreeZero C (LocalFourierKernelCoordinates.affineLine K) ⋙
    UniversalBoundedInverseImagesFromExactSystem.pull C U
      (CanonicalAffineCoefficientChange.coefficientMorphism K E 1) ⋙ sourcePullback E C U f

/-- Actual bounded inclusion followed by the SAME supplied perverse H0. -/
def perverseZero : Ambient E C 1 ⥤ (P (LocalFourierKernelCoordinates.affineLine E)).FullSubcategory :=
  (boundedProperty (C (LocalFourierKernelCoordinates.affineLine E))).ι ⋙ H0 _

/-- Ordinary H^n of the full target, then actual inverse image to its original Gm chart. -/
def targetCohomology (n : ℤ) : Ambient E C 1 ⥤ C (ArithmeticSourceMaps.fiberScheme E) :=
  cohomology C (LocalFourierKernelCoordinates.affineLine E) n ⋙
    U.pull (ArithmeticSourceMaps.localInputMorphism E E)

/-- The SAME realized heart object, H^-1, and actual target-chart inverse image. -/
def restriction : (P (LocalFourierKernelCoordinates.affineLine E)).FullSubcategory ⥤
    C (ArithmeticSourceMaps.fiberScheme E) :=
  (P _).ι ⋙ U.ordinary _ (-1) ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism E E)

/-- The original perverse-restriction law is definitional on these computed operations. -/
def perverseRestriction :
    heartRealization C P perverseBounded (LocalFourierKernelCoordinates.affineLine E) ⋙
      targetCohomology E C U (-1) ≅ restriction E C U P := Iso.refl _

/-- Lift the SAME derived compositor to the existing bounded full subcategories. -/
def boundedPullComposition {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    UniversalBoundedInverseImagesFromExactSystem.pull C U g ⋙
      UniversalBoundedInverseImagesFromExactSystem.pull C U f ≅
    UniversalBoundedInverseImagesFromExactSystem.pull C U (f ≫ g) :=
  NatIso.ofComponents
    (fun A => (boundedProperty (C X)).isoMk ((U.derivedComposition f g).app A.obj))
    (fun f => by ext; exact (U.derivedComposition _ _).hom.naturality f.hom)

/-- The phase uses the actual composite map to the ORIGINAL ordinary AS line. -/
def phasePullbackInclusion (f : FullFourierKernelCoordinates.planeScheme E ⟶
    LocalFourierKernelCoordinates.affineLine E) :
    phasePullback K E C U f ⋙ (boundedProperty
      (C (FullFourierKernelCoordinates.planeScheme E))).ι ≅
    U.degreeZero (LocalFourierKernelCoordinates.affineLine K) ⋙
      U.derivedPull (f ≫ CanonicalAffineCoefficientChange.coefficientMorphism K E 1) := by
  change (U.degreeZero (LocalFourierKernelCoordinates.affineLine K) ⋙
    U.derivedPull (CanonicalAffineCoefficientChange.coefficientMorphism K E 1)) ⋙
      U.derivedPull f ≅ _
  exact Functor.isoWhiskerLeft (U.degreeZero (LocalFourierKernelCoordinates.affineLine K))
    (U.derivedComposition f (CanonicalAffineCoefficientChange.coefficientMorphism K E 1))

/-- Exact inverse image identifies the phase with the actual ordinary pullback in degree zero. -/
def phasePullbackSingle (f : FullFourierKernelCoordinates.planeScheme E ⟶
    LocalFourierKernelCoordinates.affineLine E) :
    phasePullback K E C U f ⋙ (boundedProperty
      (C (FullFourierKernelCoordinates.planeScheme E))).ι ≅
    U.pull (f ≫ CanonicalAffineCoefficientChange.coefficientMorphism K E 1) ⋙
      U.degreeZero (FullFourierKernelCoordinates.planeScheme E) :=
  phasePullbackInclusion K E C U f ≪≫
    U.degreeZeroPullback (f ≫ CanonicalAffineCoefficientChange.coefficientMorphism K E 1)

/-- Restrict to the actual source-punctured chart, preserving the full target coordinate. -/
def chartPullback : Ambient E C 2 ⥤ Bounded C (LocalFourierKernelCoordinates.modelScheme E) :=
  UniversalBoundedInverseImagesFromExactSystem.pull C U
    (FullFourierKernelCoordinates.chartMorphism E)

/-- Actual phase pullback on the source-punctured chart, with the SAME coefficient extension. -/
def chartPhasePullback (f : LocalFourierKernelCoordinates.modelScheme E ⟶
    LocalFourierKernelCoordinates.affineLine E) :
    C (LocalFourierKernelCoordinates.affineLine K) ⥤
      Bounded C (LocalFourierKernelCoordinates.modelScheme E) :=
  boundedDegreeZero C (LocalFourierKernelCoordinates.affineLine K) ⋙
    UniversalBoundedInverseImagesFromExactSystem.pull C U
      (CanonicalAffineCoefficientChange.coefficientMorphism K E 1) ⋙
    UniversalBoundedInverseImagesFromExactSystem.pull C U f

/-- The full phase/chart compositor is computed before henselization or any trait model. -/
def chartComposition (f : FullFourierKernelCoordinates.planeScheme E ⟶
    LocalFourierKernelCoordinates.affineLine E) :
    phasePullback K E C U f ⋙ chartPullback E C U ≅
      chartPhasePullback K E C U (FullFourierKernelCoordinates.chartMorphism E ≫ f) :=
  Functor.isoWhiskerLeft
    (boundedDegreeZero C (LocalFourierKernelCoordinates.affineLine K) ⋙
      UniversalBoundedInverseImagesFromExactSystem.pull C U
        (CanonicalAffineCoefficientChange.coefficientMorphism K E 1))
    (boundedPullComposition C U (FullFourierKernelCoordinates.chartMorphism E) f)

/-- Exact standard inverse image commutes with the actual [1], on ALL bounded objects. -/
def boundedPullShift {X Y : Scheme} (f : X ⟶ Y) :
    boundedShift C Y 1 ⋙ UniversalBoundedInverseImagesFromExactSystem.pull C U f ≅
    UniversalBoundedInverseImagesFromExactSystem.pull C U f ⋙ boundedShift C X 1 :=
  NatIso.ofComponents
    (fun A => (boundedProperty (C X)).isoMk ((U.pullShift f).app A.obj))
    (fun f => by ext; exact (U.pullShift _).hom.naturality f.hom)

/-- Two actual [1] shifts convert ordinary H^-1 to H^1 on the SAME target. -/
def doubleShiftCohomology (X : Scheme) :
    boundedShift C X 1 ⋙ boundedShift C X 1 ⋙ cohomology C X (-1) ≅
      cohomology C X 1 :=
  Functor.isoWhiskerLeft (boundedProperty (C X)).ι
    (Functor.isoWhiskerRight
      (shiftFunctorAdd' (DerivedCategory (C X)) (1 : ℤ) 1 2 (by decide)).symm
      (U.ordinary X (-1)) ≪≫
    (DerivedCategory.homologyFunctor (C X) 0).shiftIso (2 : ℤ) (-1) 1 (by decide))

/-- The exact original target-chart two-shift cohomology law, on ALL bounded objects. -/
def doubleShiftTargetCohomology :
    boundedShift C (LocalFourierKernelCoordinates.affineLine E) 1 ⋙
      boundedShift C (LocalFourierKernelCoordinates.affineLine E) 1 ⋙
        targetCohomology E C U (-1) ≅ targetCohomology E C U 1 :=
  Functor.isoWhiskerRight (doubleShiftCohomology C U
    (LocalFourierKernelCoordinates.affineLine E))
    (U.pull (ArithmeticSourceMaps.localInputMorphism E E))

variable [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalCategory (DerivedCategory (C X))]
  (tensorLaws : BoundedTensorLaws C)

/-- Positive xy on the full plane, with the original AS input kept literal. -/
def fullAS (as : C (LocalFourierKernelCoordinates.affineLine K)) : Ambient E C 2 :=
  (phasePullback K E C U (FullFourierKernelCoordinates.kernelMorphism E)).obj as

/-- The SAME ordinary AS input and actual composite pullback realize fullAS in degree zero. -/
def fullASSingle (as : C (LocalFourierKernelCoordinates.affineLine K)) :
    (fullAS K E C U as).obj ≅
      (U.degreeZero (FullFourierKernelCoordinates.planeScheme E)).obj
        ((U.pull (FullFourierKernelCoordinates.kernelMorphism E ≫
          CanonicalAffineCoefficientChange.coefficientMorphism K E 1)).obj as) :=
  (phasePullbackSingle K E C U (FullFourierKernelCoordinates.kernelMorphism E)).app as

/-- Restriction of the exact fullAS gives the actual positive chart kernel. -/
def fullASChart (as : C (LocalFourierKernelCoordinates.affineLine K)) :
    (chartPullback E C U).obj (fullAS K E C U as) ≅
      (chartPhasePullback K E C U
        (LocalFourierKernelCoordinates.globalKernelMorphism E)).obj as := by
  have e := (chartComposition K E C U
    (FullFourierKernelCoordinates.kernelMorphism E)).app as
  rw [FullFourierKernelCoordinates.chart_kernelMorphism] at e
  exact e

/-- Unshifted native first projection followed by tensor with this exact AS object. -/
def sourceKernel (as : C (LocalFourierKernelCoordinates.affineLine K)) :
    Ambient E C 1 ⥤ Ambient E C 2 := by
  letI := UniversalBoundedInverseImagesFromExactSystem.boundedMonoidal C tensorLaws
    (FullFourierKernelCoordinates.planeScheme E)
  exact sourcePullback E C U (FourierOriginFromASKernel.sourceMorphism E) ⋙
    tensorRight (fullAS K E C U as)

variable (O : Operations C) (geometry : NagataGeometry) (h2 : (2 : E) ≠ 0)

/-- The only compact projection used by the original defining Fourier composites. -/
def projectionPush : Ambient E C 2 ⥤ Ambient E C 1 :=
  derivedBang C O (targetCompactification E geometry h2)

/-- The actual compactified scheme's bounded category, with the same carrier/hom universe. -/
abbrev CompactifiedAmbient : Type mu :=
  Bounded C (targetCompactification E geometry h2).compactified

/-- The SAME genuine open part of this target projection's compactification. -/
def compactify : Ambient E C 2 ⥤ CompactifiedAmbient E C geometry h2 :=
  let c := targetCompactification E geometry h2
  O.openBang c.K c.two_ne_zero c.source c.middle c.openMorphism c.open_over

/-- The SAME genuine proper part, landing on the entire native target affine line. -/
def compactifiedPush : CompactifiedAmbient E C geometry h2 ⥤ Ambient E C 1 :=
  let c := targetCompactification E geometry h2
  O.properPush c.K c.two_ne_zero c.middle c.target c.properMorphism c.proper_over

omit [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalCategory (DerivedCategory (C X))] in
/-- The native projection bang is exactly this open/proper composite. -/
theorem projectionPush_factorization :
    compactify E C O geometry h2 ⋙ compactifiedPush E C O geometry h2 =
      projectionPush E C O geometry h2 := rfl

/-- Full source realization, positive xy tensor, actual Rπ!, and [1]. -/
def derivedTransform (as : C (LocalFourierKernelCoordinates.affineLine K)) :
    (P (LocalFourierKernelCoordinates.affineLine E)).FullSubcategory ⥤ Ambient E C 1 :=
  heartRealization C P perverseBounded _ ⋙ sourceKernel K E C U tensorLaws as ⋙
    projectionPush E C O geometry h2 ⋙ boundedShift C _ 1

/-- The target is the entire affine line, including y=0. -/
def transform (as : C (LocalFourierKernelCoordinates.affineLine K)) :
    (P (LocalFourierKernelCoordinates.affineLine E)).FullSubcategory ⥤
      (P (LocalFourierKernelCoordinates.affineLine E)).FullSubcategory :=
  derivedTransform K E C U P perverseBounded tensorLaws O geometry h2 as ⋙
    perverseZero E C P H0

omit [∀ X, MonoidalCategory (C X)] in
/-- The exact full kernel underlying object, before any selected source object or cycles. -/
theorem sourceKernel_obj (as : C (LocalFourierKernelCoordinates.affineLine K))
    (A : Ambient E C 1) :
    ((sourceKernel K E C U tensorLaws as).obj A).obj =
      (U.derivedPull (FourierOriginFromASKernel.sourceMorphism E)).obj A.obj ⊗
        (fullAS K E C U as).obj := rfl

/-- The target uses the polynomial second coordinate without inverting it. -/
theorem target_zero_coordinate :
    (FullFourierKernelCoordinates.targetHom E).toRingHom
      (MvPolynomial.X (0 : Fin 1)) = MvPolynomial.X (1 : Fin 2) := by
  simp [FullFourierKernelCoordinates.targetHom]

/-- An actual rational point of the full native affine plane. -/
def planePoint (x y : E) : Spec (.of E) ⟶ FullFourierKernelCoordinates.planeScheme E :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y)))

/-- An actual rational point of the full native target line, including zero. -/
def linePoint (y : E) : Spec (.of E) ⟶ LocalFourierKernelCoordinates.affineLine E :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ : Fin 1 => y)))

/-- The native target projection sends (x,0) to the actual target origin. -/
theorem target_origin_point (x : E) :
    planePoint E x 0 ≫ FullFourierKernelCoordinates.targetMorphism E = linePoint E 0 := by
  dsimp only [planePoint, linePoint, FullFourierKernelCoordinates.targetMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply MvPolynomial.ringHom_ext
  · intro c; simp [FullFourierKernelCoordinates.targetHom]
  · intro i; simp [FullFourierKernelCoordinates.targetHom]

/-- The positive full-plane kernel is defined and zero on the actual target origin. -/
theorem kernel_target_origin (x : E) :
    planePoint E x 0 ≫ FullFourierKernelCoordinates.kernelMorphism E = linePoint E 0 := by
  dsimp only [planePoint, linePoint, FullFourierKernelCoordinates.kernelMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply MvPolynomial.ringHom_ext
  · intro c; simp [FullFourierKernelCoordinates.kernelHom]
  · intro i; simp [FullFourierKernelCoordinates.kernelHom]

end PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.affineStructure
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.affineStructure_locallyFiniteType
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.affinePresentation
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.target_over
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.source_over
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.kernel_coefficient_square
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.target_locallyFiniteType
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.CompactificationOver
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.NagataGeometry
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.compactification
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.targetCompactification
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.Ambient
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.boundedShift
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.heartRealization
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.heartRealization_full
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.heartRealization_faithful
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.heartRealizationFullyFaithful
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.sourcePullback
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.phasePullback
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.perverseZero
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.targetCohomology
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.restriction
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.perverseRestriction
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.boundedPullComposition
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.phasePullbackInclusion
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.phasePullbackSingle
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.chartPullback
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.chartPhasePullback
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.chartComposition
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.boundedPullShift
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.doubleShiftCohomology
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.doubleShiftTargetCohomology
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.fullAS
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.fullASSingle
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.fullASChart
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.sourceKernel
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.projectionPush
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.CompactifiedAmbient
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.compactify
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.compactifiedPush
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.projectionPush_factorization
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.derivedTransform
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.transform
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.sourceKernel_obj
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.target_zero_coordinate
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.planePoint
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.linePoint
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.target_origin_point
#print axioms PrimeGap182.TypeIII.FullFourierCoreFromNativeBoundedOperations.kernel_target_origin
