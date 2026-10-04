import TypeIIIPrimitiveRadialFromParameter
import TypeIIIFullFourierKernelCoordinates
import TypeIIIPublishedFourierRules
import TypeIIIPublishedTypeIII

/-!
# Linear radial phase descent from the original pole objects

The field being supplied is `LocalRules.linear_pullback_phase_baseChange`.
No independently chosen phase set or rescaled-phase equality is an input.
Membership in the ORIGINAL PhaseData.phases is recognized by nonzero Hom
from the stalks of the same AS source along the actual pole morphisms.
Field transport and trait scaling are equivalences; they transport those
original Hom witnesses, including the coefficient-zero character.

The common derived-origin realization remains explicit framework data.
Its inverse images are indexed by actual scheme maps. Ordinary H^-1 and
H^-2, the linear perverse [1] shift, and their compatibility are explicit.
The algebraic radial/linear square is proved before taking the common
henselian generic-origin inverse image and wild stalk.

Intended general framework provenance: inverse-image composition and base
change in Laumon §0.5, AS inverse-image functoriality in §1.1, and ordinary
cohomology/perverse smooth pullback in BBD §§1.3 and 4.0. These are general
adic realization premises, not a direct citation for the conclusion below.
https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf
https://publications.ias.edu/sites/default/files/Faisceaux%20pervers.pdf
No common sheaf model or complete Type III input family is constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport
open PublishedPhaseApplication PublishedFourierRules
open LocalFourierKernelCoordinates FullFourierKernelCoordinates
open StartingSourceMaps GenericCurvePullback FourierSourceMaps PrimitiveRadialAS

universe c d e f g h i j l
variable {k : Type} [Field k] [IsAlgClosed k]

abbrev L (k : Type) [Field k] := PhaseField k

/-- Full affine radial parameter, before the common generic-origin stalk. -/
abbrev originScheme (k : Type) [Field k] : Scheme :=
  Spec (.of (Polynomial (L k)))

/-- Canonical affine-line base-field morphism, with no independent map
choice: its ring map extends polynomial coefficients by algebraMap. -/
def baseLineMorphism (k0 k : Type) [Field k0] [Field k] [Algebra k0 k] :
    StartingSourceMaps.affineLine k ⟶ StartingSourceMaps.affineLine k0 :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k0 k)))

def linearHom (a b : k) : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (fun _ =>
    MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1)

def radialHom : MvPolynomial (Fin 2) k →ₐ[k] Polynomial (L k) :=
  MvPolynomial.aeval (fun n =>
    if n = 0 then Polynomial.X ^ 2 else Polynomial.C (direction k) * Polynomial.X ^ 2)

def squareHom (u : L k) : MvPolynomial (Fin 1) k →ₐ[k] Polynomial (L k) :=
  MvPolynomial.aeval (fun _ => (Polynomial.C u * Polynomial.X) ^ 2)

def linearMorphism (a b : k) : planeScheme k ⟶ LocalFourierKernelCoordinates.affineLine k :=
  Spec.map (CommRingCat.ofHom (linearHom a b).toRingHom)

def radialMorphism : originScheme k ⟶ planeScheme k :=
  Spec.map (CommRingCat.ofHom (radialHom (k := k)).toRingHom)

def squareMorphism (u : L k) : originScheme k ⟶ LocalFourierKernelCoordinates.affineLine k :=
  Spec.map (CommRingCat.ofHom (squareHom u).toRingHom)

def originScalarHom (u : (L k)ˣ) : Polynomial (L k) →ₐ[k] Polynomial (L k) :=
  (Polynomial.aeval (Polynomial.C (u : L k) * Polynomial.X)).restrictScalars k

def originScalarMorphism (u : (L k)ˣ) : originScheme k ⟶ originScheme k :=
  Spec.map (CommRingCat.ofHom (originScalarHom u).toRingHom)

def originConstantHom (σ : L k ≃ₐ[k] L k) : Polynomial (L k) →ₐ[k] Polynomial (L k) :=
  Polynomial.mapAlgHom σ.toAlgHom

def originConstantMorphism (σ : L k ≃ₐ[k] L k) : originScheme k ⟶ originScheme k :=
  Spec.map (CommRingCat.ofHom (originConstantHom σ).toRingHom)

omit [IsAlgClosed k] in
theorem originScalarHom_square (u : (L k)ˣ) :
    (originScalarHom u).comp (squareHom 1) = squareHom (u : L k) := by
  apply MvPolynomial.algHom_ext
  intro n
  simp [originScalarHom, squareHom]

omit [IsAlgClosed k] in
theorem originConstantHom_square (σ : L k ≃ₐ[k] L k) :
    (originConstantHom σ).comp (squareHom 1) = squareHom (1 : L k) := by
  apply MvPolynomial.algHom_ext
  intro n
  simp [originConstantHom, squareHom]

omit [IsAlgClosed k] in
theorem originScalarMorphism_square (u : (L k)ˣ) :
    originScalarMorphism u ≫ squareMorphism 1 = squareMorphism (u : L k) := by
  dsimp only [originScalarMorphism, squareMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (originScalarHom_square u))

omit [IsAlgClosed k] in
theorem originConstantMorphism_square (σ : L k ≃ₐ[k] L k) :
    originConstantMorphism σ ≫ squareMorphism 1 = squareMorphism (1 : L k) := by
  dsimp only [originConstantMorphism, squareMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (originConstantHom_square σ))

/-- Constant-field automorphism holding the trait coordinate fixed. -/
def constantHom (σ : L k ≃ₐ[k] L k) : LocalRing k →ₐ[k] LocalRing k where
  toRingHom := LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp σ.toRingHom)
    (PhysicalTorusLaurent.variableUnit (L k))
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap k (L k) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    change LaurentPolynomial.C (σ (algebraMap k (L k) c)) = _
    rw [σ.commutes]
    rfl

def constantMorphism (σ : L k ≃ₐ[k] L k) : localScheme k ⟶ localScheme k :=
  Spec.map (CommRingCat.ofHom (constantHom σ).toRingHom)

omit [IsAlgClosed k] in
theorem constantHom_pole (σ : L k ≃ₐ[k] L k) (c : L k) :
    (constantHom σ).comp (PrimitiveRadialAS.poleHom k c) =
      PrimitiveRadialAS.poleHom k (σ c) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, PrimitiveRadialAS.poleHom, MvPolynomial.aeval_X]
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C c * LaurentPolynomial.T (-1)) = _
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_neg_one]
  rfl

omit [IsAlgClosed k] in
theorem constantMorphism_pole (σ : L k ≃ₐ[k] L k) (c : L k) :
    constantMorphism σ ≫ poleMorphism k c = poleMorphism k (σ c) := by
  dsimp only [constantMorphism, poleMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (constantHom_pole σ c))

omit [IsAlgClosed k] in
theorem scalarMorphism_pole (u : (L k)ˣ) (c : L k) :
    Spec.map (CommRingCat.ofHom (scalarHom k u).toRingHom) ≫
      poleMorphism k c = poleMorphism k (c / (u : L k)) := by
  dsimp only [poleMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (poleHom_scalar_comp k c u))

omit [IsAlgClosed k] in
theorem radial_linearHom (a b : k) (u : L k)
    (hu : u ^ 2 = algebraMap k (L k) a + algebraMap k (L k) b * direction k) :
    (radialHom (k := k)).comp (linearHom a b) = squareHom u := by
  apply MvPolynomial.algHom_ext
  intro n
  simp only [AlgHom.comp_apply, linearHom, radialHom, squareHom,
    MvPolynomial.aeval_X, map_add, map_mul, MvPolynomial.aeval_C,
    ite_eq_left, show (1 : Fin 2) ≠ 0 from by decide, mul_pow]
  change Polynomial.C (algebraMap k (L k) a) * Polynomial.X ^ 2 +
    Polynomial.C (algebraMap k (L k) b) *
      (Polynomial.C (direction k) * Polynomial.X ^ 2) = _
  rw [← Polynomial.C_pow, hu, Polynomial.C_add, Polynomial.C_mul]
  ring

omit [IsAlgClosed k] in
/-- The actual square is valid at the affine origin as well. -/
theorem radial_linearMorphism (a b : k) (u : L k)
    (hu : u ^ 2 = algebraMap k (L k) a + algebraMap k (L k) b * direction k) :
    radialMorphism (k := k) ≫ linearMorphism a b = squareMorphism u := by
  dsimp only [radialMorphism, linearMorphism, squareMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (radial_linearHom a b u hu))

variable {E : Type e} [Field E] {G : Type g} [Group G]
  {Obj : Type c} {CurveObj : Type d}
  (F : FourierData k Obj CurveObj)
  (radial : Obj → FDRep E G)

/-- One common derived-origin model. H^-1/H^-2 here are ordinary
cohomology followed by the SAME generic-zero wild stalk. `curveRealization`
uses the original CurveObj and `linearRealization` the original linearPullback.
The trait operations are actual equivalences in the intended model;
the abstract record does not itself instantiate that geometric model. -/
structure DerivedOrigin where
  CurveDerived : Type f
  [curveCategory : Category.{h} CurveDerived]
  PlaneDerived : Type f
  [planeCategory : Category.{h} PlaneDerived]
  OriginDerived : Type i
  [originCategory : Category.{j} OriginDerived]
  curveRealization : CurveObj → CurveDerived
  planeRealization : Obj → PlaneDerived
  linearInverseImage : (planeScheme k ⟶ LocalFourierKernelCoordinates.affineLine k) →
    (CurveDerived ⥤ PlaneDerived)
  curveInverseImage : (originScheme k ⟶ LocalFourierKernelCoordinates.affineLine k) →
    (CurveDerived ⥤ OriginDerived)
  originInverseImage : (originScheme k ⟶ originScheme k) → (OriginDerived ⥤ OriginDerived)
  radialInverseImage : PlaneDerived ⥤ OriginDerived
  planeShiftOne : PlaneDerived ⥤ PlaneDerived
  originShiftOne : OriginDerived ⥤ OriginDerived
  minusOne : OriginDerived ⥤ FDRep E G
  minusTwo : OriginDerived ⥤ FDRep E G
  originScale : (L k)ˣ → (OriginDerived ≌ OriginDerived)
  traitScale : (L k)ˣ → (FDRep E G ≌ FDRep E G)
  [scaleZero : ∀ u, (traitScale u).functor.PreservesZeroMorphisms]
  [scaleInverseZero : ∀ u, (traitScale u).inverse.PreservesZeroMorphisms]
  originTwist : (L k ≃ₐ[k] L k) → (OriginDerived ≌ OriginDerived)
  traitTwist : (L k ≃ₐ[k] L k) → (FDRep E G ≌ FDRep E G)
  [twistZero : ∀ σ, (traitTwist σ).functor.PreservesZeroMorphisms]
  composition : ∀ f, linearInverseImage f ⋙ radialInverseImage ≅
    curveInverseImage (radialMorphism ≫ f)
  radialShift : planeShiftOne ⋙ radialInverseImage ≅
    radialInverseImage ⋙ originShiftOne
  ordinaryShift : originShiftOne ⋙ minusTwo ≅ minusOne
  originComposition : ∀ f g, curveInverseImage g ⋙ originInverseImage f ≅
    curveInverseImage (f ≫ g)
  scaleRealization : ∀ u, originInverseImage (originScalarMorphism u) ≅ (originScale u).functor
  twistRealization : ∀ σ, originInverseImage (originConstantMorphism σ) ≅ (originTwist σ).functor
  scaleCohomology : ∀ u, (originScale u).functor ⋙ minusOne ≅
    minusOne ⋙ (traitScale u).functor
  twistCohomology : ∀ σ, (originTwist σ).functor ⋙ minusOne ≅
    minusOne ⋙ (traitTwist σ).functor
  linearRealization : ∀ Q a b, (a, b) ≠ (0, 0) →
    (planeRealization (F.linearPullback (a, b) Q) ≅
      planeShiftOne.obj ((linearInverseImage (linearMorphism a b)).obj (curveRealization Q)))
  radialStalk : ∀ P, radial P ≅
    minusTwo.obj (radialInverseImage.obj (planeRealization P))

attribute [instance] DerivedOrigin.curveCategory DerivedOrigin.planeCategory
  DerivedOrigin.originCategory DerivedOrigin.scaleZero DerivedOrigin.scaleInverseZero
  DerivedOrigin.twistZero

variable {F radial} (O : DerivedOrigin F radial)

/-- Generic ZERO-origin stalk of the original curve object after Y^2,
using ordinary H^-1. This is unrelated to the source infinity functor. -/
def DerivedOrigin.curveStalk (Q : CurveObj) : FDRep E G :=
  O.minusOne.obj ((O.curveInverseImage (squareMorphism 1)).obj (O.curveRealization Q))

/-- Full-affine scaling comparison is derived from general inverse-image
composition and the actual square-coordinate identity. -/
def DerivedOrigin.scaleInverseImage (u : (L k)ˣ) :
    O.curveInverseImage (squareMorphism 1) ⋙ (O.originScale u).functor ≅
      O.curveInverseImage (squareMorphism (u : L k)) := by
  have e := O.originComposition (originScalarMorphism u) (squareMorphism 1)
  rw [originScalarMorphism_square u] at e
  exact Functor.isoWhiskerLeft _ (O.scaleRealization u).symm ≪≫ e

/-- Constant transport of the original curve is derived because sigma
fixes the square map over k, before taking ordinary H^-1 or the stalk. -/
def DerivedOrigin.constantInverseImage (σ : L k ≃ₐ[k] L k) :
    O.curveInverseImage (squareMorphism 1) ⋙ (O.originTwist σ).functor ≅
      O.curveInverseImage (squareMorphism 1) := by
  have e := O.originComposition (originConstantMorphism σ) (squareMorphism 1)
  rw [originConstantMorphism_square σ] at e
  exact Functor.isoWhiskerLeft _ (O.twistRealization σ).symm ≪≫ e

/-- Derive the common-stalk comparison from actual inverse-image
composition, the algebraic square, and the ordinary [1] shift identity. -/
def DerivedOrigin.linearStalkComparison (Q : CurveObj) (a b : k)
    (hab : (a, b) ≠ (0, 0)) (u : (L k)ˣ)
    (hu : (u : L k) ^ 2 = algebraMap k (L k) a +
      algebraMap k (L k) b * direction k) :
    (O.traitScale u).functor.obj (O.curveStalk Q) ≅
      radial (F.linearPullback (a, b) Q) := by
  let C := O.curveRealization Q
  let R := (O.linearInverseImage (linearMorphism a b)).obj C
  have plane : radial (F.linearPullback (a, b) Q) ≅
      O.minusOne.obj ((O.curveInverseImage (squareMorphism (u : L k))).obj C) := by
    have e := (O.composition (linearMorphism a b)).app C
    rw [radial_linearMorphism a b (u : L k) hu] at e
    exact O.radialStalk _ ≪≫
      O.minusTwo.mapIso (O.radialInverseImage.mapIso (O.linearRealization Q a b hab)) ≪≫
      O.minusTwo.mapIso ((O.radialShift).app R) ≪≫
      (O.ordinaryShift).app (O.radialInverseImage.obj R) ≪≫ O.minusOne.mapIso e
  exact ((O.scaleCohomology u).app
    ((O.curveInverseImage (squareMorphism 1)).obj C)).symm ≪≫
      O.minusOne.mapIso ((O.scaleInverseImage u).app C) ≪≫ plane.symm

/-- Constant-field functorial inverse image of the SAME curve gives
the same generic-origin representation after twisting. -/
def DerivedOrigin.constantStalkComparison (Q : CurveObj) (σ : L k ≃ₐ[k] L k) :
    (O.traitTwist σ).functor.obj (O.curveStalk Q) ≅ O.curveStalk Q :=
  ((O.twistCohomology σ).app
    ((O.curveInverseImage (squareMorphism 1)).obj (O.curveRealization Q))).symm ≪≫
      O.minusOne.mapIso ((O.constantInverseImage σ).app (O.curveRealization Q))

variable {Line : Type} [Category.{l} Line] (as : Line)
  (D : PhaseData k E G)

/-- AS functoriality and recognition of the ORIGINAL phases. Characters
are defined by actual poleMorphism pullbacks of one original AS source.
The source category may be defined over a smaller constant field: first
embed its ordinary object in degree zero and pull along the fixed
baseFieldMorphism, then along the k-pole map. In the prime application
sourceLineScheme is A1 over Fp and baseFieldMorphism is A1_k to A1_Fp.
The scaling/field laws are functorial comparisons, not phase equalities. -/
structure PoleTransport (O : DerivedOrigin F radial) (sourceLineScheme : Scheme)
    (baseFieldMorphism : StartingSourceMaps.affineLine k ⟶ sourceLineScheme) where
  LineDerived : Type f
  [lineDerivedCategory : Category.{h} LineDerived]
  CoefficientLineDerived : Type f
  [coefficientLineCategory : Category.{h} CoefficientLineDerived]
  TraitDerived : Type i
  [traitDerivedCategory : Category.{j} TraitDerived]
  lineDegreeZero : Line ⥤ LineDerived
  baseFieldInverseImage : (StartingSourceMaps.affineLine k ⟶ sourceLineScheme) →
    (LineDerived ⥤ CoefficientLineDerived)
  poleInverseImage : (localScheme k ⟶ StartingSourceMaps.affineLine k) →
    (CoefficientLineDerived ⥤ TraitDerived)
  traitInverseImage : (localScheme k ⟶ localScheme k) → (TraitDerived ⥤ TraitDerived)
  wildStalk : TraitDerived ⥤ FDRep E G
  composition : ∀ f g, poleInverseImage g ⋙ traitInverseImage f ≅ poleInverseImage (f ≫ g)
  scaleCohomology : ∀ u, traitInverseImage
    (Spec.map (CommRingCat.ofHom (scalarHom k u).toRingHom)) ⋙ wildStalk ≅
      wildStalk ⋙ (O.traitScale u).functor
  twistCohomology : ∀ σ, traitInverseImage (constantMorphism σ) ⋙ wildStalk ≅
      wildStalk ⋙ (O.traitTwist σ).functor
  membership : ∀ R, D.HasProfile R → ∀ c,
    c ∈ D.phases R ↔
      ∃ f : wildStalk.obj ((poleInverseImage (poleMorphism k c)).obj
        ((baseFieldInverseImage baseFieldMorphism).obj (lineDegreeZero.obj as))) ⟶ R, f ≠ 0

attribute [instance] PoleTransport.lineDerivedCategory PoleTransport.coefficientLineCategory
  PoleTransport.traitDerivedCategory

variable {as D O} {sourceLineScheme : Scheme}
  {baseFieldMorphism : StartingSourceMaps.affineLine k ⟶ sourceLineScheme}
  (T : PoleTransport as D O sourceLineScheme baseFieldMorphism)

def PoleTransport.poleStalk (f : localScheme k ⟶ StartingSourceMaps.affineLine k) :
    Line ⥤ FDRep E G := T.lineDegreeZero ⋙ T.baseFieldInverseImage baseFieldMorphism ⋙
      T.poleInverseImage f ⋙ T.wildStalk

def PoleTransport.character (c : L k) : FDRep E G :=
  (T.poleStalk (poleMorphism k c)).obj as

/-- AS scaling is derived from the actual beta/T map identity and
functorial inverse image; this includes beta=0. -/
def PoleTransport.scalePole (u : (L k)ˣ) (c : L k) :
    (O.traitScale u).functor.obj (T.character c) ≅ T.character (c / (u : L k)) := by
  have e := (T.composition
    (Spec.map (CommRingCat.ofHom (scalarHom k u).toRingHom)) (poleMorphism k c)).app
      ((T.baseFieldInverseImage baseFieldMorphism).obj (T.lineDegreeZero.obj as))
  rw [scalarMorphism_pole u c] at e
  exact ((T.scaleCohomology u).app
    ((T.poleInverseImage (poleMorphism k c)).obj
      ((T.baseFieldInverseImage baseFieldMorphism).obj (T.lineDegreeZero.obj as)))).symm ≪≫
      T.wildStalk.mapIso e

/-- AS field transport fixes the trait coordinate and applies sigma to
the original pole coefficient, by the proved scheme-map identity. -/
def PoleTransport.twistPole (σ : L k ≃ₐ[k] L k) (c : L k) :
    (O.traitTwist σ).functor.obj (T.character c) ≅ T.character (σ c) := by
  have e := (T.composition (constantMorphism σ) (poleMorphism k c)).app
    ((T.baseFieldInverseImage baseFieldMorphism).obj (T.lineDegreeZero.obj as))
  rw [constantMorphism_pole σ c] at e
  exact ((T.twistCohomology σ).app
    ((T.poleInverseImage (poleMorphism k c)).obj
      ((T.baseFieldInverseImage baseFieldMorphism).obj (T.lineDegreeZero.obj as)))).symm ≪≫
      T.wildStalk.mapIso e

/-- An equivalence transports a nonzero ORIGINAL Hom witness. -/
theorem homWitness_transport {C : Type f} [Category.{h} C] [HasZeroMorphisms C]
    (e : C ≌ C) [e.functor.PreservesZeroMorphisms]
    {X Y X' Y' : C} (ex : e.functor.obj X ≅ X') (ey : e.functor.obj Y ≅ Y')
    (f : X ⟶ Y) (hf : f ≠ 0) :
    ∃ g : X' ⟶ Y', g ≠ 0 := by
  refine ⟨ex.inv ≫ e.functor.map f ≫ ey.hom, ?_⟩
  intro hz
  have hleft : ex.inv ≫ (e.functor.map f ≫ ey.hom) = ex.inv ≫ 0 := by
    simpa only [Category.assoc, comp_zero] using hz
  have hright : e.functor.map f ≫ ey.hom = 0 ≫ ey.hom := by
    simpa only [zero_comp] using (cancel_epi ex.inv).mp hleft
  have hmap : e.functor.map f = e.functor.map 0 := by
    simpa only [Functor.map_zero] using (cancel_mono ey.hom).mp hright
  exact hf (e.functor.map_injective hmap)

variable (profile : ∀ P, F.HasSimpleRadialPhases P ↔ D.HasProfile (radial P))
  (phases : ∀ P, F.phases P = D.phases (radial P))

include O T profile phases in
omit [IsAlgClosed k] in
/-- The EXACT existing LocalRules field, derived by transporting Hom
witnesses through the common original curve stalk and back. There are no
rectangle parameters, phase exclusions, or nonzero-coefficient guards. -/
theorem linear_pullback_phase_baseChange (Q : CurveObj) (a b : k)
    (hab : (a, b) ≠ (0, 0)) (hp : F.HasSimpleRadialPhases (F.linearPullback (a, b) Q))
    (u : L k) (hu : u ^ 2 = algebraMap (RatFunc k) (L k)
      (RatFunc.C a + RatFunc.C b * RatFunc.X))
    (σ : L k ≃ₐ[k] L k) (x : L k)
    (hx : x ∈ (fun β => u * β) '' F.phases (F.linearPullback (a, b) Q)) :
    σ x ∈ (fun β => u * β) '' F.phases (F.linearPullback (a, b) Q) := by
  have hu0 : u ≠ 0 := linearDirectionRoot_ne_zero a b hab u hu
  let U : (L k)ˣ := Units.mk0 u hu0
  have hs : (U : L k) ^ 2 = algebraMap k (L k) a +
      algebraMap k (L k) b * direction k := by
    simpa only [U, Units.val_mk0, map_add, map_mul, phaseField_map_C, direction] using hu
  let P := F.linearPullback (a, b) Q
  have hP : D.HasProfile (radial P) := (profile P).mp hp
  have e := O.linearStalkComparison Q a b hab U hs
  obtain ⟨β, hβ, rfl⟩ := hx
  have hβD : β ∈ D.phases (radial P) := by
    rw [← phases P]
    exact hβ
  obtain ⟨f, hf⟩ := (T.membership (radial P) hP β).mp hβD
  have ec : (O.traitScale U).functor.obj (T.character (u * β)) ≅ T.character β := by
    simpa only [PoleTransport.character, U, Units.val_mk0,
      mul_div_cancel_left₀ β hu0] using T.scalePole U (u * β)
  obtain ⟨g, hg⟩ := homWitness_transport (O.traitScale U).symm
    (((O.traitScale U).unitIso.app (T.character (u * β))) ≪≫
      (O.traitScale U).inverse.mapIso ec).symm
    (((O.traitScale U).unitIso.app (O.curveStalk Q)) ≪≫
      (O.traitScale U).inverse.mapIso e).symm f hf
  obtain ⟨h, hh⟩ := homWitness_transport (O.traitTwist σ)
    (T.twistPole σ (u * β)) (O.constantStalkComparison Q σ) g hg
  obtain ⟨j, hj⟩ := homWitness_transport (O.traitScale U)
    (T.scalePole U (σ (u * β))) e h hh
  refine ⟨σ (u * β) / u, ?_, ?_⟩
  · rw [phases P]
    apply (T.membership (radial P) hP _).mpr
    simpa only [U, Units.val_mk0, PoleTransport.character] using ⟨j, hj⟩
  · exact mul_div_cancel₀ _ hu0

/-- All other LocalRules remain the original scoped general laws. Only
the rescaled-phase field is supplied by this genuine transport application. -/
structure OtherLocalRules (S : PublishedSupportRules.SurfaceData k Obj)
    (C : PublishedSupportRules.CoefficientTransport S) : Prop where
  support_isomorphic : ∀ {A B}, C.Isomorphic A B → S.support A = S.support B
  profile_isomorphic : ∀ {A B}, C.Isomorphic A B →
    (F.HasSimpleRadialPhases A ↔ F.HasSimpleRadialPhases B)
  phases_isomorphic : ∀ {A B}, C.Isomorphic A B → F.phases A = F.phases B
  inverse_constituent : ∀ P Q, Q ∈ S.constituents (F.fourier P) →
    ∃ A ∈ S.constituents P, C.Isomorphic (F.inverse Q) A
  profile_constituent : ∀ P A, F.HasSimpleRadialPhases P →
    A ∈ S.constituents P → F.HasSimpleRadialPhases A
  phases_constituent : ∀ P A, F.HasSimpleRadialPhases P →
    A ∈ S.constituents P → F.phases A ⊆ F.phases P
  phases_nonempty : ∀ A, F.HasSimpleRadialPhases A →
    S.support A = Set.univ → (F.phases A).Nonempty
  inverse_point_zero_phase : ∀ Q, S.Simple Q → ∀ z : k × k,
    S.support Q = {z} → (0 : L k) ∈ F.phases (F.inverse Q)
  inverse_line_pullback : ∀ Q, S.Simple Q → ∀ a b : k,
    (a ≠ 0 ∨ b ≠ 0) → S.support Q ⊆ ScalingLines.originLine a b →
    ∃ J : CurveObj, C.Isomorphic (F.inverse Q) (F.linearPullback (b, -a) J)

include O T profile phases in
omit [IsAlgClosed k] in
theorem localRules {S : PublishedSupportRules.SurfaceData k Obj}
    {C : PublishedSupportRules.CoefficientTransport S} (R : OtherLocalRules (F := F) S C) :
    LocalRules S C F where
  support_isomorphic := R.support_isomorphic
  profile_isomorphic := R.profile_isomorphic
  phases_isomorphic := R.phases_isomorphic
  inverse_constituent := R.inverse_constituent
  profile_constituent := R.profile_constituent
  phases_constituent := R.phases_constituent
  phases_nonempty := R.phases_nonempty
  inverse_point_zero_phase := R.inverse_point_zero_phase
  inverse_line_pullback := R.inverse_line_pullback
  linear_pullback_phase_baseChange := linear_pullback_phase_baseChange (O := O) T profile phases

/-- Exactly the original generic Theory premises, with LocalRules split
to remove ONLY its linear-pullback phase base-change conclusion.
This is not a copy or renaming of the root actual-family Inputs record. -/
structure TheoryData (p : ℕ) [Fact p.Prime] where
  Obj : Type c
  CurveObj : Type d
  data : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj
  bbd : PublishedSupportRules.BBDRules data
  qst : PublishedSupportRules.QSTRules data
  classification : PublishedSupportRules.SupportClassification data
  degrees : PublishedSupportRules.OrdinarySupportDegreeRules data
  coefficient : PublishedSupportRules.CoefficientTransport data
  fourier : FourierData (AlgebraicClosure (ZMod p)) Obj CurveObj
  otherLocalRules : OtherLocalRules (F := fourier) data coefficient
  realization : PublishedSupportRules.RationalStalkRealization p data
  traceWeights : PublishedStalkCertificate.TraceWeightRules p data realization fourier.fourier

/-- Root integration can use this accessor in every dependent field type.
The original curve/plane objects and FourierData are retained literally.
The common origin, ordinary cohomology and AS realization are explicit
general framework premises; no complete geometric model is constructed. -/
def TheoryData.toTheory {p : ℕ} [Fact p.Prime] (A : TheoryData.{c, d} p)
    {E : Type e} [Field E] {G : Type g} [Group G]
    (radial : A.Obj → FDRep E G)
    {Line : Type} [Category.{l} Line] (as : Line)
    (D : PhaseData (AlgebraicClosure (ZMod p)) E G)
    (O : DerivedOrigin A.fourier radial)
    (T : PoleTransport as D O (StartingSourceMaps.affineLine (ZMod p))
      (baseLineMorphism (ZMod p) (AlgebraicClosure (ZMod p))))
    (profile : ∀ P, A.fourier.HasSimpleRadialPhases P ↔ D.HasProfile (radial P))
    (phases : ∀ P, A.fourier.phases P = D.phases (radial P)) :
    PublishedTypeIII.Theory.{c, d} p where
  Obj := A.Obj
  CurveObj := A.CurveObj
  data := A.data
  bbd := A.bbd
  qst := A.qst
  classification := A.classification
  degrees := A.degrees
  coefficient := A.coefficient
  fourier := A.fourier
  localRules := localRules T profile phases A.otherLocalRules
  realization := A.realization
  traceWeights := A.traceWeights

end PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport

#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.radial_linearMorphism
#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.DerivedOrigin.linearStalkComparison
#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.DerivedOrigin.constantStalkComparison
#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.homWitness_transport
#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.linear_pullback_phase_baseChange
#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.localRules
#print axioms PrimeGap182.TypeIII.LinearRadialPhaseFromPoleTransport.TheoryData.toTheory
