import TypeIIIOriginRealizationFromExactInverseImages
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# One ordinary system for the native origin and original AS poles

The original B categories are retained literally. The extra indices are
actual A1_k, FULL A2_k, Spec L[t], the actual punctured Spec L[t,t^-1],
and arbitrary additional schemes. All derived operations use the SAME
standard localization of ONE ordinary inverse-image system. The origin
ordinary wild functor is punctured inverse image followed by ONE ordinary
wildLocal; the pole derived wild functor is ordinary H^0 followed by that
same functor. Actual coordinate squares and exact ordinary inverse images
construct both scaling/constant comparisons. Original ambient objects,
smooth linear[1], radial comparison, ordinary wild-group transport and
the general ORIGINAL AS-character membership dictionary remain explicit.
No target phase equality, rectangle exclusion or full adic model is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.OriginPoleFromExactInverseImages
open PublishedFourierRules PublishedPhaseApplication
open ExactInverseImagesToDerived LinearRadialPhaseFromPoleTransport

universe w c dc e g

abbrev Extra (J : Type) := OriginRealizationFromExactInverseImages.Index ⊕ (PUnit ⊕ J)

variable {K0 k J : Type} [Field K0] [Field k]

def extraScheme (k : Type) [Field k] (otherScheme : J → Scheme) : Extra J → Scheme :=
  Sum.elim (OriginRealizationFromExactInverseImages.scheme k)
    (Sum.elim (fun _ => FourierSourceMaps.localScheme k) otherScheme)

def extraObjects (NC : OriginRealizationFromExactInverseImages.Index → Type)
    (LC : Type) (OC : J → Type) : Extra J → Type :=
  Sum.elim NC (Sum.elim (fun _ => LC) OC)

variable (B : SourceInverseImageSystem.System.{0,w} K0)
  (otherScheme : J → Scheme)
  (NC : OriginRealizationFromExactInverseImages.Index → Type)
  [∀ i, Category.{w} (NC i)] [∀ i, Abelian (NC i)]
  (LC : Type) [Category.{w} LC] [Abelian LC]
  (OC : J → Type) [∀ i, Category.{w} (OC i)] [∀ i, Abelian (OC i)]

instance extraCategory : ∀ i, Category.{w} (extraObjects NC LC OC i) := by
  intro i
  cases i with
  | inl n => change Category.{w} (NC n); infer_instance
  | inr rest => cases rest with
    | inl _ => change Category.{w} LC; infer_instance
    | inr n => change Category.{w} (OC n); infer_instance

instance extraAbelian : ∀ i, Abelian (extraObjects NC LC OC i) := by
  intro i
  cases i with
  | inl n => change Abelian (NC n); infer_instance
  | inr rest => cases rest with
    | inl _ => change Abelian LC; infer_instance
    | inr n => change Abelian (OC n); infer_instance

abbrev CommonIndex := SourceInverseImageSystem.Space K0 ⊕ Extra J

def nativeIndex (i : OriginRealizationFromExactInverseImages.Index) : CommonIndex (K0 := K0) (J := J) :=
  Sum.inr (Sum.inl i)

def traitIndex : CommonIndex (K0 := K0) (J := J) := Sum.inr (Sum.inr (Sum.inl PUnit.unit))

def sourceIndex : CommonIndex (K0 := K0) (J := J) := Sum.inl .line

variable {B otherScheme NC LC OC}
  (A : OrdinarySystem (extensionScheme (extraScheme k otherScheme))
    (extensionObjects B (extraObjects NC LC OC)))

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{w}
    (extensionObjects B (extraObjects NC LC OC) i) :=
  fun i => HasDerivedCategory.standard (extensionObjects B (extraObjects NC LC OC) i)

/-- Literal restriction of the ONE ordinary system to the three native
scheme indices; no replacement category or pullback is selected. -/
def nativeSystem : OrdinarySystem (OriginRealizationFromExactInverseImages.scheme k) NC where
  pull {i j} f := A.pull (i := nativeIndex i) (j := nativeIndex j) f
  identity i := A.identity (nativeIndex i)
  composition {i j l} f g := A.composition (i := nativeIndex i) (j := nativeIndex j) (k := nativeIndex l) f g
  additive {i j} f := inferInstanceAs ((A.pull (i := nativeIndex i) (j := nativeIndex j) f).Additive)
  limits {i j} f := inferInstanceAs (PreservesFiniteLimits (A.pull (i := nativeIndex i) (j := nativeIndex j) f))
  colimits {i j} f := inferInstanceAs (PreservesFiniteColimits (A.pull (i := nativeIndex i) (j := nativeIndex j) f))

/-- The actual punctured inclusion, over the SAME phase field L. -/
def puncturedOpen (k : Type) [Field k] :
    FourierSourceMaps.localScheme k ⟶ originScheme k :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial (L k) →+* LaurentPolynomial (L k)))

theorem scalarOpenHom (u : (L k)ˣ) :
    (FourierSourceMaps.scalarHom k u).toRingHom.comp Polynomial.toLaurent =
      Polynomial.toLaurent.comp (originScalarHom u).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [FourierSourceMaps.scalarHom, originScalarHom]
  · simp [FourierSourceMaps.scalarHom, originScalarHom,
      PhysicalTorusLaurent.variableUnit]

theorem constantOpenHom (σ : L k ≃ₐ[k] L k) :
    (constantHom σ).toRingHom.comp Polynomial.toLaurent =
      Polynomial.toLaurent.comp (originConstantHom σ).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [constantHom, originConstantHom]
  · simp [constantHom, originConstantHom, PhysicalTorusLaurent.variableUnit]

theorem scalarOpen_square (u : (L k)ˣ) :
    puncturedOpen k ≫ originScalarMorphism u =
      FourierSourceMaps.scalarMorphism k u ≫ puncturedOpen k := by
  dsimp only [puncturedOpen, originScalarMorphism, FourierSourceMaps.scalarMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (scalarOpenHom u).symm

theorem constantOpen_square (σ : L k ≃ₐ[k] L k) :
    puncturedOpen k ≫ originConstantMorphism σ = constantMorphism σ ≫ puncturedOpen k := by
  dsimp only [puncturedOpen, originConstantMorphism, constantMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (constantOpenHom σ).symm

variable {E : Type e} [Field E] {G : Type g} [Group G]

/-- The only ordinary wild/group framework, on the common punctured
index and ORIGINAL representation category. -/
structure OrdinaryWild where
  wildLocal : LC ⥤ FDRep E G
  traitScale : (L k)ˣ → (FDRep E G ≌ FDRep E G)
  traitTwist : (L k ≃ₐ[k] L k) → (FDRep E G ≌ FDRep E G)
  [scaleZero : ∀ u, (traitScale u).functor.PreservesZeroMorphisms]
  [scaleInverseZero : ∀ u, (traitScale u).inverse.PreservesZeroMorphisms]
  [twistZero : ∀ σ, (traitTwist σ).functor.PreservesZeroMorphisms]
  scaleWildLocal : ∀ u, A.pull (i := traitIndex) (j := traitIndex)
    (FourierSourceMaps.scalarMorphism k u) ⋙ wildLocal ≅ wildLocal ⋙ (traitScale u).functor
  twistWildLocal : ∀ σ, A.pull (i := traitIndex) (j := traitIndex)
    (constantMorphism σ) ⋙ wildLocal ≅ wildLocal ⋙ (traitTwist σ).functor

attribute [instance] OrdinaryWild.scaleZero OrdinaryWild.scaleInverseZero OrdinaryWild.twistZero

variable {A} (W : OrdinaryWild (E := E) (G := G) A)

def OrdinaryWild.originWild : NC .origin ⥤ FDRep E G :=
  A.pull (i := traitIndex) (j := nativeIndex .origin) (puncturedOpen k) ⋙ W.wildLocal

def OrdinaryWild.originScale :
    ∀ u, (nativeSystem A).pull (i := .origin) (j := .origin) (originScalarMorphism u) ⋙ W.originWild ≅
      W.originWild ⋙ (W.traitScale u).functor := fun u =>
  (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (A.composition (i := traitIndex) (j := nativeIndex .origin) (k := nativeIndex .origin)
        (puncturedOpen k) (originScalarMorphism u) ≪≫
        eqToIso (congrArg (fun f => A.pull (i := traitIndex) (j := nativeIndex .origin) f)
          (scalarOpen_square u)) ≪≫
        (A.composition (i := traitIndex) (j := traitIndex) (k := nativeIndex .origin)
          (FourierSourceMaps.scalarMorphism k u) (puncturedOpen k)).symm) W.wildLocal ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft _ (W.scaleWildLocal u) ≪≫ (Functor.associator ..).symm

def OrdinaryWild.originTwist :
    ∀ σ, (nativeSystem A).pull (i := .origin) (j := .origin) (originConstantMorphism σ) ⋙ W.originWild ≅
      W.originWild ⋙ (W.traitTwist σ).functor := fun σ =>
  (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (A.composition (i := traitIndex) (j := nativeIndex .origin) (k := nativeIndex .origin)
        (puncturedOpen k) (originConstantMorphism σ) ≪≫
        eqToIso (congrArg (fun f => A.pull (i := traitIndex) (j := nativeIndex .origin) f)
          (constantOpen_square σ)) ≪≫
        (A.composition (i := traitIndex) (j := traitIndex) (k := nativeIndex .origin)
          (constantMorphism σ) (puncturedOpen k)).symm) W.wildLocal ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft _ (W.twistWildLocal σ) ≪≫ (Functor.associator ..).symm

variable {Obj : Type c} {CurveObj : Type dc}
  (F : FourierData k Obj CurveObj) (radial : Obj → FDRep E G)

local instance nativeDerived : ∀ i, HasDerivedCategory.{w} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

/-- ONLY the four original-object geometric application comparisons. -/
structure OriginalObjects where
  curveRealization : CurveObj → (nativeSystem A).Derived .curve
  planeRealization : Obj → (nativeSystem A).Derived .plane
  linearRealization : ∀ Q a b, (a, b) ≠ (0, 0) →
    (planeRealization (F.linearPullback (a, b) Q) ≅ ((nativeSystem A).shiftOne .plane).obj
      (((nativeSystem A).derivedPull (i := .plane) (j := .curve) (linearMorphism a b)).obj (curveRealization Q)))
  radialStalk : ∀ P, radial P ≅ ((nativeSystem A).ordinary .origin (-2) ⋙ W.originWild).obj
    (((nativeSystem A).derivedPull (i := .origin) (j := .plane) (radialMorphism (k := k))).obj (planeRealization P))

variable {F radial} (R : OriginalObjects W F radial)

def OriginalObjects.toApplication :
    OriginRealizationFromExactInverseImages.Application (nativeSystem A) F radial where
  wild := W.originWild
  traitScale := W.traitScale
  traitTwist := W.traitTwist
  scaleWild := W.originScale
  twistWild := W.originTwist
  curveRealization := R.curveRealization
  planeRealization := R.planeRealization
  linearRealization := R.linearRealization
  radialStalk := R.radialStalk

def OriginalObjects.nativeOrigin : DerivedOrigin F radial := R.toApplication.origin

local instance traitDerived : HasDerivedCategory.{w} LC := HasDerivedCategory.standard LC

variable [Algebra K0 k]
  (as : B.Obj .line) (D : PhaseData k E G)

def OrdinaryWild.ordinaryCharacter (beta : L k) : FDRep E G :=
  W.wildLocal.obj ((A.pull (i := traitIndex) (j := nativeIndex .curve)
    (PrimitiveRadialAS.poleMorphism k beta)).obj
    ((A.pull (i := nativeIndex .curve) (j := sourceIndex)
      (baseLineMorphism K0 k)).obj as))

def OrdinaryWild.derivedCharacter (beta : L k) : FDRep E G :=
  (A.ordinary traitIndex 0 ⋙ W.wildLocal).obj
    ((A.derivedPull (i := traitIndex) (j := nativeIndex .curve)
      (PrimitiveRadialAS.poleMorphism k beta)).obj
      ((A.derivedPull (i := nativeIndex .curve) (j := sourceIndex)
        (baseLineMorphism K0 k)).obj ((A.degreeZero sourceIndex).obj as)))

/-- Exact inverse images preserve the degree-zero ORIGINAL AS source.
H^0 then recovers the same ordinary character, including coefficient0. -/
def OrdinaryWild.characterIso (beta : L k) :
    W.derivedCharacter as beta ≅ W.ordinaryCharacter as beta :=
  (A.ordinary traitIndex 0 ⋙ W.wildLocal).mapIso
    ((A.derivedPull (i := traitIndex) (j := nativeIndex .curve)
      (PrimitiveRadialAS.poleMorphism k beta)).mapIso
      ((A.degreeZeroPullback (i := nativeIndex .curve) (j := sourceIndex)
        (baseLineMorphism K0 k)).app as) ≪≫
      (A.degreeZeroPullback (i := traitIndex) (j := nativeIndex .curve)
        (PrimitiveRadialAS.poleMorphism k beta)).app
        ((A.pull (i := nativeIndex .curve) (j := sourceIndex)
          (baseLineMorphism K0 k)).obj as)) ≪≫
    W.wildLocal.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso LC 0).app _)

/-- General AS character recognition for EVERY original profiled
representation; not a target radial or rectangle phase conclusion. -/
structure ASRecognition : Prop where
  membership : ∀ X, D.HasProfile X → ∀ beta,
    beta ∈ D.phases X ↔ ∃ f : W.ordinaryCharacter as beta ⟶ X, f ≠ 0

/-- A categorical isomorphism preserves nonzero Hom witnesses. -/
theorem homWitness_isoLeft {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} (e : X ≅ Y) :
    (∃ f : X ⟶ Z, f ≠ 0) ↔ ∃ f : Y ⟶ Z, f ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨e.inv ≫ f, ?_⟩
    intro h
    apply hf
    have h' := congrArg (fun q => e.hom ≫ q) h
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, comp_zero] using h'
  · rintro ⟨f, hf⟩
    refine ⟨e.hom ≫ f, ?_⟩
    intro h
    apply hf
    have h' := congrArg (fun q => e.inv ≫ q) h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, comp_zero] using h'

variable {as D} (H : ASRecognition W as D)

/-- ALL PoleTransport operations/comparisons are constructed on the
same ordinary system and the same wildLocal/traitScale/traitTwist. -/
def OriginalObjects.toPole : PoleTransport as D R.nativeOrigin
    (StartingSourceMaps.affineLine K0) (baseLineMorphism K0 k) where
  LineDerived := A.Derived sourceIndex
  CoefficientLineDerived := A.Derived (nativeIndex .curve)
  TraitDerived := A.Derived traitIndex
  lineDegreeZero := A.degreeZero sourceIndex
  baseFieldInverseImage f := A.derivedPull (i := nativeIndex .curve) (j := sourceIndex) f
  poleInverseImage f := A.derivedPull (i := traitIndex) (j := nativeIndex .curve) f
  traitInverseImage f := A.derivedPull (i := traitIndex) (j := traitIndex) f
  wildStalk := A.ordinary traitIndex 0 ⋙ W.wildLocal
  composition f q := A.derivedComposition (i := traitIndex) (j := traitIndex) (k := nativeIndex .curve) f q
  scaleCohomology u := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (OriginRealizationFromExactInverseImages.exactDerivedCohomology
        (A.pull (i := traitIndex) (j := traitIndex) (FourierSourceMaps.scalarMorphism k u)) 0) _ ≪≫
    Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ (W.scaleWildLocal u) ≪≫
    (Functor.associator ..).symm
  twistCohomology σ := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (OriginRealizationFromExactInverseImages.exactDerivedCohomology
        (A.pull (i := traitIndex) (j := traitIndex) (constantMorphism σ)) 0) _ ≪≫
    Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ (W.twistWildLocal σ) ≪≫
    (Functor.associator ..).symm
  membership X hX beta := (H.membership X hX beta).trans
    (homWitness_isoLeft (W.characterIso as beta)).symm

/-- Original pull coherence can be carried alongside the constructor;
it is the ordinary extension realization, not a derived target law. -/
def OriginalObjects.toPoleWithOriginalAgreement
    (_agreement : OriginalPullAgreement B (extraScheme k otherScheme)
      (extraObjects NC LC OC) A) : PoleTransport as D R.nativeOrigin
      (StartingSourceMaps.affineLine K0) (baseLineMorphism K0 k) := OriginalObjects.toPole W R H

end PrimeGap182.TypeIII.OriginPoleFromExactInverseImages

#print axioms PrimeGap182.TypeIII.OriginPoleFromExactInverseImages.scalarOpen_square
#print axioms PrimeGap182.TypeIII.OriginPoleFromExactInverseImages.constantOpen_square
#print axioms PrimeGap182.TypeIII.OriginPoleFromExactInverseImages.OrdinaryWild.characterIso
#print axioms PrimeGap182.TypeIII.OriginPoleFromExactInverseImages.OriginalObjects.toApplication
#print axioms PrimeGap182.TypeIII.OriginPoleFromExactInverseImages.OriginalObjects.toPole
