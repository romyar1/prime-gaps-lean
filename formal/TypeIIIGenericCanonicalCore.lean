import TypeIIIGenericCohomologyBaseChange
import TypeIIICohomologyInputTransport
import TypeIIIPulledCurveInput

/-!
# The original generic parabolic image and the constructed pulled input

Use the same curve inverse image in compact base change and in the
three-factor input recipe. Functoriality of forgetting supports transports
the already proved parabolic base change across the proved input
isomorphism. Both original cohomology maps remain compatible.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.GenericCanonicalCore

open StartingSourceMaps GenericSourceSpecialization GenericCurvePullback
open GenericCohomologyBaseChange CohomologyInputTransport PulledCurveInput
open PublishedPhysicalConstruction ParabolicBaseChange OrdinaryBaseChangeFromDuality

universe u v w z a b c d e f g
variable (K : Type u) [Field K]
  {Input : Type v} [Category.{w} Input] {Point : Type z}
  {C : Type a} [Category.{b} C] [Abelian C]
  {Input' : Type c} [Category.{d} Input'] {Point' : Type e}
  {C' : Type f} [Category.{g} C'] [Abelian C']

variable (D : CurveData Input Point) (CR : CurveRules D)
  {H : CohomologyData Input C} {P : ParameterData C} (G : CohomologyRules D H P)
  (DT : Cᵒᵖ ⥤ C) (S : RelativeDuality D (H := H) (P := P) DT)
  (D' : CurveData Input' Point') (CR' : CurveRules D')
  {H' : CohomologyData Input' C'} {P' : ParameterData C'}
  (G' : CompactLissityRules D' (H := H') (P := P'))
  (DT' : C'ᵒᵖ ⥤ C') (S' : RelativeDuality D' (H := H') (P := P') DT')
  (CF : CompactFunctor (H' := H'))
  (O : InverseImages K (Input := Input) (Input' := Input') (C := C) (C' := C'))

/- Compact base change, fiber properties and dual compatibility for
every coordinate-preserving Cartesian square. There is no ordinary-cohomology field. -/
variable (CB : ∀ (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (g : genericScheme K ⟶ sourceScheme K),
    CoordinateBaseChange K g f →
      CompactBaseChange D DT D' DT' (O.base f) (O.curve g).obj (H := H) (H' := H') (P := P))

/- Naturality of the compact pairing, with the same general compact
base-change maps, for every coordinate-preserving square and every good input. -/
variable (PN : ∀ (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (g : genericScheme K ⟶ sourceScheme K)
    (sq : CoordinateBaseChange K g f),
    CompactPairingBaseChange D CR G DT S D' DT' S' (O.base f) (O.curve g).obj CF (CB f g sq))

variable (alpha m n : Kˣ)

variable [(O.base (radialParameterMorphism K alpha m n)).Additive]
  [PreservesFiniteLimits (O.base (radialParameterMorphism K alpha m n))]
  [PreservesFiniteColimits (O.base (radialParameterMorphism K alpha m n))]


variable [MonoidalCategory Input] [MonoidalCategory Input']
  [(O.curve (specializationMorphism K alpha m n)).Monoidal]
  (RP : PullbackProperties D D' (O.curve (specializationMorphism K alpha m n)))
  (tensorSource : ∀ A B, D.tensor A B ≅ A ⊗ B)
  (tensorTarget : ∀ A B, D'.tensor A B ≅ A ⊗ B)
  (HC : FunctorialCohomology H')

/-- Identify pullback of the ORIGINAL parabolic image with the core
constructed from the literal pulled factors. No input or image
identification is a premise. -/
def genericCanonicalCoreIso (A : KloostermanInputData D) :
    (O.base (radialParameterMorphism K alpha m n)).obj (parabolicCore H A.input) ≅
      parabolicCore H' (pulledInput D D'
        (O.curve (specializationMorphism K alpha m n)) RP A).input :=
  genericParabolicBaseChangeIso K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n A ≪≫
    parabolicInputIso H' HC (pulledInputIso D D'
      (O.curve (specializationMorphism K alpha m n)) RP tensorSource tensorTarget A)

theorem genericCanonicalCoreIso_fromCompact (A : KloostermanInputData D) :
    (O.base (radialParameterMorphism K alpha m n)).map
        (Abelian.factorThruImage (H.comparison A.input)) ≫
      (genericCanonicalCoreIso K D CR G DT S D' CR' G' DT' S' CF O CB PN
        alpha m n RP tensorSource tensorTarget HC A).hom =
      ((CB _ _ (genericSourceSquare_coordinateBaseChange K alpha m n)).compact A.input (A.input_lisse CR)).hom ≫
        (compactIso H' HC (pulledInputIso D D'
          (O.curve (specializationMorphism K alpha m n)) RP tensorSource tensorTarget A)).hom ≫
        Abelian.factorThruImage (H'.comparison (pulledInput D D'
          (O.curve (specializationMorphism K alpha m n)) RP A).input) := by
  simp only [genericCanonicalCoreIso, Iso.trans_hom]
  rw [← Category.assoc, genericParabolicBaseChangeIso_fromCompact,
    Category.assoc, fromCompact_parabolicInputIso]

theorem genericCanonicalCoreIso_toOrdinary (A : KloostermanInputData D) :
    (genericCanonicalCoreIso K D CR G DT S D' CR' G' DT' S' CF O CB PN
        alpha m n RP tensorSource tensorTarget HC A).hom ≫
      Abelian.image.ι (H'.comparison (pulledInput D D'
        (O.curve (specializationMorphism K alpha m n)) RP A).input) =
      (O.base (radialParameterMorphism K alpha m n)).map (Abelian.image.ι (H.comparison A.input)) ≫
        ((genericGoodBaseChange K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n).ordinary
          ⟨A.input, input_good D CR A⟩).hom ≫
        (ordinaryIso H' HC (pulledInputIso D D'
          (O.curve (specializationMorphism K alpha m n)) RP tensorSource tensorTarget A)).hom := by
  simp only [genericCanonicalCoreIso, Iso.trans_hom]
  rw [Category.assoc, parabolicInputIso_toOrdinary,
    ← Category.assoc, genericParabolicBaseChangeIso_toOrdinary, Category.assoc]

end PrimeGap182.TypeIII.GenericCanonicalCore

#print axioms PrimeGap182.TypeIII.GenericCanonicalCore.genericCanonicalCoreIso
#print axioms PrimeGap182.TypeIII.GenericCanonicalCore.genericCanonicalCoreIso_fromCompact
#print axioms PrimeGap182.TypeIII.GenericCanonicalCore.genericCanonicalCoreIso_toOrdinary
