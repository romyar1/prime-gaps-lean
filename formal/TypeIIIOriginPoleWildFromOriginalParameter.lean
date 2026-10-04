import TypeIIIOriginPoleFromExactInverseImages
import TypeIIIConstantFieldLocalData
import TypeIIIPrimitiveRadialFromParameter

/-!
# Bind the common wild stalk to the ORIGINAL parameter stalk

The phase-field isomorphism is the existing algebraic-closure-uniqueness
construction, fixing the original constants and generic direction.
Its Laurent extension constructs an actual isomorphism from the new
punctured origin to the ORIGINAL B parameter scheme. The new wildLocal
is inverse-map ordinary pull followed by the ORIGINAL J, with no freely
selected wild functor. Actual pole coordinate identities, ordinary
composition and OriginalPullAgreement identify every new AS character
with the old parameter character at the inverse phase-field coefficient,
including coefficient0. The original general group transports and
original all-profiled AS-character membership remain explicit; current
PhaseLaws/PhaseRules alone do not provide the latter theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter
open PublishedPhaseApplication OriginPoleFromExactInverseImages ExactInverseImagesToDerived
open PhaseFieldConstants

universe w c dc e g
variable {K0 k Jx : Type} [Field K0] [Field k] [Algebra K0 k] [Algebra.IsAlgebraic K0 k]

/-- Laurent extension of a coefficient field isomorphism, fixing T. -/
def laurentMap {R S : Type} [Field R] [Field S] (e : R ≃+* S) :
    LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp e.toRingHom)
    (PhysicalTorusLaurent.variableUnit S)

theorem laurentMap_inverse {R S : Type} [Field R] [Field S] (e : R ≃+* S) :
    (laurentMap e.symm).comp (laurentMap e) = RingHom.id (LaurentPolynomial R) := by
  apply SourceCurveBaseChange.laurent_ringHom_ext
  · apply RingHom.ext
    intro a
    simp [laurentMap]
  · apply Units.ext
    change laurentMap e.symm (laurentMap e (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
    simp [laurentMap, PhysicalTorusLaurent.variableUnit]

/-- The canonical EXISTING phase-field equivalence, not an independent
coefficient identification or family comparison. -/
def parameterIso : FourierSourceMaps.localScheme k ≅ GenericCurvePullback.parameterScheme K0 where
  hom := Spec.map (CommRingCat.ofHom (laurentMap (phaseFieldEquiv K0 k)))
  inv := Spec.map (CommRingCat.ofHom (laurentMap (phaseFieldEquiv K0 k).symm))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (laurentMap (phaseFieldEquiv K0 k)).comp (laurentMap (phaseFieldEquiv K0 k).symm) =
        RingHom.id (LaurentPolynomial (PhaseField k)) := by
      simpa only [RingEquiv.symm_symm] using (laurentMap_inverse (phaseFieldEquiv K0 k).symm)
    rw [h]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [laurentMap_inverse (phaseFieldEquiv K0 k)]
    exact Spec.map_id _

theorem poleHom_C (K : Type) [Field K] (beta : PhaseField K) (a : K) :
    (PrimitiveRadialAS.poleHom K beta).toRingHom (MvPolynomial.C a) =
      LaurentPolynomial.C (algebraMap K (PhaseField K) a) := by
  change (MvPolynomial.aeval (fun _ : Fin 1 => LaurentPolynomial.C beta * LaurentPolynomial.T (-1))) (MvPolynomial.C a) = _
  rw [MvPolynomial.aeval_C]
  rfl

theorem poleHom_X (K : Type) [Field K] (beta : PhaseField K) (n : Fin 1) :
    (PrimitiveRadialAS.poleHom K beta).toRingHom (MvPolynomial.X n) =
      LaurentPolynomial.C beta * LaurentPolynomial.T (-1) := by
  change (MvPolynomial.aeval (fun _ : Fin 1 => LaurentPolynomial.C beta * LaurentPolynomial.T (-1))) (MvPolynomial.X n) = _
  rw [MvPolynomial.aeval_X]

theorem poleCoordinateHom (beta : PhaseField k) :
    (laurentMap (phaseFieldEquiv K0 k).symm).comp
      ((PrimitiveRadialAS.poleHom k beta).toRingHom.comp (MvPolynomial.map (algebraMap K0 k))) =
    (PrimitiveRadialAS.poleHom K0 ((phaseFieldEquiv K0 k).symm beta)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C, poleHom_C, poleHom_C]
    rw [laurentMap, LaurentPolynomial.eval₂_C, RingHom.comp_apply,
      ← phaseFieldEquiv_constant K0 k a]
    exact congrArg LaurentPolynomial.C (RingEquiv.symm_apply_apply _ _)
  · intro n
    rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X, poleHom_X, poleHom_X]
    simp [laurentMap, PhysicalTorusLaurent.variableUnit]

/-- The actual old/new pole identity for ALL coefficients. -/
theorem poleCoordinate_square (beta : PhaseField k) :
    (parameterIso (K0 := K0) (k := k)).inv ≫ PrimitiveRadialAS.poleMorphism k beta ≫
      LinearRadialPhaseFromPoleTransport.baseLineMorphism K0 k =
      PrimitiveRadialAS.poleMorphism K0 ((phaseFieldEquiv K0 k).symm beta) := by
  dsimp only [parameterIso, PrimitiveRadialAS.poleMorphism,
    LinearRadialPhaseFromPoleTransport.baseLineMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (poleCoordinateHom beta)

/-- The ORIGINAL parameter automorphism induced by conjugating the
actual new trait automorphism, with no separate old-map selection. -/
def conjugateTrait (f : FourierSourceMaps.localScheme k ⟶ FourierSourceMaps.localScheme k) :
    GenericCurvePullback.parameterScheme K0 ⟶ GenericCurvePullback.parameterScheme K0 :=
  (parameterIso (K0 := K0) (k := k)).inv ≫ f ≫ (parameterIso (K0 := K0) (k := k)).hom

theorem conjugateTrait_square
    (f : FourierSourceMaps.localScheme k ⟶ FourierSourceMaps.localScheme k) :
    conjugateTrait (K0 := K0) f ≫ (parameterIso (K0 := K0) (k := k)).inv =
      (parameterIso (K0 := K0) (k := k)).inv ≫ f := by
  simp only [conjugateTrait, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (B : SourceInverseImageSystem.System.{0,w} K0)
  (otherScheme : Jx → Scheme)
  (NC : OriginRealizationFromExactInverseImages.Index → Type)
  [∀ i, Category.{w} (NC i)] [∀ i, Abelian (NC i)]
  (LC : Type) [Category.{w} LC] [Abelian LC]
  (OC : Jx → Type) [∀ i, Category.{w} (OC i)] [∀ i, Abelian (OC i)]

variable {B otherScheme NC LC OC}
  (A : OrdinarySystem (extensionScheme (extraScheme k otherScheme))
    (extensionObjects B (extraObjects NC LC OC)))
  (agreement : OriginalPullAgreement B (extraScheme k otherScheme) (extraObjects NC LC OC) A)
  {E : Type e} [Field E] {G : Type g} [Group G]
  (J : B.Obj .parameter ⥤ FDRep E G)

def parameterIndex : CommonIndex (K0 := K0) (J := Jx) := Sum.inl .parameter

/-- General group transport on the ORIGINAL B parameter stalk J;
there is no new arbitrary wildLocal field. -/
structure OriginalGroupTransport where
  traitScale : (PhaseField k)ˣ → (FDRep E G ≌ FDRep E G)
  traitTwist : (PhaseField k ≃ₐ[k] PhaseField k) → (FDRep E G ≌ FDRep E G)
  [scaleZero : ∀ u, (traitScale u).functor.PreservesZeroMorphisms]
  [scaleInverseZero : ∀ u, (traitScale u).inverse.PreservesZeroMorphisms]
  [twistZero : ∀ sigma, (traitTwist sigma).functor.PreservesZeroMorphisms]
  parameterScale : ∀ u, B.pull (X := .parameter) (Y := .parameter)
    (conjugateTrait (K0 := K0) (FourierSourceMaps.scalarMorphism k u)) ⋙ J ≅
      J ⋙ (traitScale u).functor
  parameterTwist : ∀ sigma, B.pull (X := .parameter) (Y := .parameter)
    (conjugateTrait (K0 := K0) (LinearRadialPhaseFromPoleTransport.constantMorphism sigma)) ⋙ J ≅
      J ⋙ (traitTwist sigma).functor

attribute [instance] OriginalGroupTransport.scaleZero OriginalGroupTransport.scaleInverseZero
  OriginalGroupTransport.twistZero

variable {A agreement J} (T : OriginalGroupTransport (k := k) J)

def boundWildLocal : LC ⥤ FDRep E G :=
  A.pull (i := parameterIndex) (j := traitIndex) (parameterIso (K0 := K0) (k := k)).inv ⋙ J

/-- Construct the SAME ordinary wild framework using original J,
actual conjugation, ordinary composition and original pull agreement. -/
def OriginalGroupTransport.toOrdinaryWild : OrdinaryWild (E := E) (G := G) A where
  wildLocal := boundWildLocal (A := A) (J := J)
  traitScale := T.traitScale
  traitTwist := T.traitTwist
  scaleWildLocal u := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (A.composition (i := parameterIndex) (j := traitIndex) (k := traitIndex)
        (parameterIso (K0 := K0) (k := k)).inv (FourierSourceMaps.scalarMorphism k u) ≪≫
        eqToIso (congrArg (fun f => A.pull (i := parameterIndex) (j := traitIndex) f)
          (conjugateTrait_square (K0 := K0) (FourierSourceMaps.scalarMorphism k u)).symm) ≪≫
        (A.composition (i := parameterIndex) (j := parameterIndex) (k := traitIndex)
          (conjugateTrait (K0 := K0) (FourierSourceMaps.scalarMorphism k u))
          (parameterIso (K0 := K0) (k := k)).inv).symm) J ≪≫
      Functor.associator .. ≪≫ Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (eqToIso (agreement.pull (i := .parameter) (j := .parameter)
          (conjugateTrait (K0 := K0) (FourierSourceMaps.scalarMorphism k u)))) J ≪≫
          T.parameterScale u) ≪≫ (Functor.associator ..).symm
  twistWildLocal sigma := (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (A.composition (i := parameterIndex) (j := traitIndex) (k := traitIndex)
        (parameterIso (K0 := K0) (k := k)).inv
        (LinearRadialPhaseFromPoleTransport.constantMorphism sigma) ≪≫
        eqToIso (congrArg (fun f => A.pull (i := parameterIndex) (j := traitIndex) f)
          (conjugateTrait_square (K0 := K0)
            (LinearRadialPhaseFromPoleTransport.constantMorphism sigma)).symm) ≪≫
        (A.composition (i := parameterIndex) (j := parameterIndex) (k := traitIndex)
          (conjugateTrait (K0 := K0) (LinearRadialPhaseFromPoleTransport.constantMorphism sigma))
          (parameterIso (K0 := K0) (k := k)).inv).symm) J ≪≫
      Functor.associator .. ≪≫ Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (eqToIso (agreement.pull (i := .parameter) (j := .parameter)
          (conjugateTrait (K0 := K0) (LinearRadialPhaseFromPoleTransport.constantMorphism sigma)))) J ≪≫
          T.parameterTwist sigma) ≪≫ (Functor.associator ..).symm

variable (as : B.Obj .line) (PD : PhaseData K0 E G)

def oldCharacter (beta : PhaseField K0) : FDRep E G :=
  PrimitiveRadialAS.phase K0 (PrimitiveRadialFromParameter.parameterRestriction B) J as beta

/-- Every newly constructed ordinary character is the ORIGINAL
parameter/J character at inverse phase-field coefficient, including0. -/
def OriginalGroupTransport.characterComparison (beta : PhaseField k) :
    (T.toOrdinaryWild (agreement := agreement)).ordinaryCharacter as beta ≅
      oldCharacter (J := J) as ((phaseFieldEquiv K0 k).symm beta) :=
  J.mapIso
    ((A.composition (i := parameterIndex) (j := traitIndex) (k := nativeIndex .curve)
      (parameterIso (K0 := K0) (k := k)).inv (PrimitiveRadialAS.poleMorphism k beta)).app
      ((A.pull (i := nativeIndex .curve) (j := sourceIndex)
        (LinearRadialPhaseFromPoleTransport.baseLineMorphism K0 k)).obj as) ≪≫
      (A.composition (i := parameterIndex) (j := nativeIndex .curve) (k := sourceIndex)
        ((parameterIso (K0 := K0) (k := k)).inv ≫ PrimitiveRadialAS.poleMorphism k beta)
        (LinearRadialPhaseFromPoleTransport.baseLineMorphism K0 k)).app as ≪≫
      (eqToIso (congrArg (fun f => A.pull (i := parameterIndex) (j := sourceIndex) f)
        (poleCoordinate_square beta))).app as ≪≫
      (eqToIso (agreement.pull (i := .parameter) (j := .line)
        (PrimitiveRadialAS.poleMorphism K0 ((phaseFieldEquiv K0 k).symm beta)))).app as)

/-- Precisely the original GENERAL all-profiled parameter-character
recognition. Existing singleton PhaseLaws do not imply this law. -/
structure OriginalASRecognition : Prop where
  membership : ∀ X, PD.HasProfile X → ∀ beta,
    beta ∈ PD.phases X ↔ ∃ f : oldCharacter (J := J) as beta ⟶ X, f ≠ 0

variable {as PD}

theorem image_phase_iff (beta : PhaseField k) (X : FDRep E G) :
    beta ∈ (ConstantFieldLocalData.phaseData K0 k PD).phases X ↔
      (phaseFieldEquiv K0 k).symm beta ∈ PD.phases X := by
  change beta ∈ phaseFieldEquiv K0 k '' PD.phases X ↔ _
  constructor
  · rintro ⟨old, hold, he⟩
    rw [← he, RingEquiv.symm_apply_apply]
    exact hold
  · intro h
    exact ⟨(phaseFieldEquiv K0 k).symm beta, h, RingEquiv.apply_symm_apply _ _⟩

/-- NEW membership is derived from ORIGINAL PD/parameter/J recognition,
using the actual old/new character and coefficient comparisons. -/
theorem OriginalGroupTransport.toASRecognition (H : OriginalASRecognition (J := J) as PD) :
    ASRecognition (T.toOrdinaryWild (agreement := agreement)) as
      (ConstantFieldLocalData.phaseData K0 k PD) where
  membership X hX beta := (image_phase_iff (PD := PD) beta X).trans
    ((H.membership X hX ((phaseFieldEquiv K0 k).symm beta)).trans
      (homWitness_isoLeft (T.characterComparison (agreement := agreement) as beta)).symm)

end PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter

#print axioms PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter.parameterIso
#print axioms PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter.poleCoordinate_square
#print axioms PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter.OriginalGroupTransport.toOrdinaryWild
#print axioms PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter.OriginalGroupTransport.characterComparison
#print axioms PrimeGap182.TypeIII.OriginPoleWildFromOriginalParameter.OriginalGroupTransport.toASRecognition
