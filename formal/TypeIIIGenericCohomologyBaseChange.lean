import TypeIIIOrdinaryBaseChangeFromDuality
import TypeIIIGenericCurvePullback

/-!
# Apply compact base change to the proved generic Cartesian square

The general laws quantify over coordinate-preserving Cartesian squares
between these source and parameter schemes. The existing generic radial
square is proved Cartesian with its curve coordinate fixed, so its
cohomology comparison is constructed without
a supplied family-specific square, ordinary base-change map or image
comparison. Both original cohomology maps are preserved.

The inverse-image functors, compact base-change and compact-pairing
naturality are still general sheaf-theoretic inputs. A common realization
with the Kl3/AS and Fourier operations remains to be assembled.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.GenericCohomologyBaseChange

open StartingSourceMaps GenericSourceSpecialization GenericCurvePullback
open PublishedPhysicalConstruction ParabolicBaseChange OrdinaryBaseChangeFromDuality

universe u v w z a b c d e f g
variable (K : Type u) [Field K]
  {Input : Type v} [Category.{w} Input] {Point : Type z}
  {C : Type a} [Category.{b} C] [Abelian C]
  {Input' : Type c} [Category.{d} Input'] {Point' : Type e}
  {C' : Type f} [Category.{g} C'] [Abelian C']

/-- Inverse images on all morphisms between the fixed geometric spaces.
The curve part is a functor on objects and morphisms. -/
structure InverseImages where
  base : (parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K) → C ⥤ C'
  curve : (genericScheme K ⟶ sourceScheme K) → Input ⥤ Input'

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
every coordinate-preserving Cartesian square. Retaining the coordinate
is essential for the separate zero-tameness and infinity-slope laws.
There is no ordinary-cohomology field. -/
variable (CB : ∀ (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (g : genericScheme K ⟶ sourceScheme K),
    CoordinateBaseChange K g f →
      CompactBaseChange D DT D' DT' (O.base f) (O.curve g).obj (H := H) (H' := H') (P := P))

/- Naturality of the compact pairing, with the same general compact
base-change maps, for every coordinate-preserving square and good input. -/
variable (PN : ∀ (f : parameterScheme K ⟶ PhysicalTorusMorphism.torusScheme K)
    (g : genericScheme K ⟶ sourceScheme K)
    (sq : CoordinateBaseChange K g f),
    CompactPairingBaseChange D CR G DT S D' DT' S' (O.base f) (O.curve g).obj CF (CB f g sq))

variable (alpha m n : Kˣ)

/-- The geometric square hypothesis is discharged by its checked ring
pushout. Ordinary base change is derived by relative duality. -/
def genericGoodBaseChange :
    CohomologyBaseChange (goodCohomology D (H := H)) H'
      (O.base (radialParameterMorphism K alpha m n))
      (fun A => (O.curve (specializationMorphism K alpha m n)).obj A.val) :=
  goodCohomologyBaseChange D CR G DT S D' CR' G' DT' S'
    (O.base (radialParameterMorphism K alpha m n))
    (O.curve (specializationMorphism K alpha m n)).obj CF
    (CB _ _ (genericSourceSquare_coordinateBaseChange K alpha m n))
    (PN _ _ (genericSourceSquare_coordinateBaseChange K alpha m n))

variable [(O.base (radialParameterMorphism K alpha m n)).Additive]
  [PreservesFiniteLimits (O.base (radialParameterMorphism K alpha m n))]
  [PreservesFiniteColimits (O.base (radialParameterMorphism K alpha m n))]

/-- Pullback of the original Type III parabolic image is the image on
the exact generic curve, with all input admissibility proofs derived. -/
def genericParabolicBaseChangeIso (A : KloostermanInputData D) :
    (O.base (radialParameterMorphism K alpha m n)).obj (parabolicCore H A.input) ≅
      parabolicCore H' ((O.curve (specializationMorphism K alpha m n)).obj A.input) :=
  parabolicBaseChangeIso (goodCohomology D (H := H)) H'
    (O.base (radialParameterMorphism K alpha m n))
    (fun A => (O.curve (specializationMorphism K alpha m n)).obj A.val)
    (genericGoodBaseChange K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n)
    ⟨A.input, input_good D CR A⟩

theorem genericParabolicBaseChangeIso_fromCompact (A : KloostermanInputData D) :
    (O.base (radialParameterMorphism K alpha m n)).map
        (Abelian.factorThruImage (H.comparison A.input)) ≫
      (genericParabolicBaseChangeIso K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n A).hom =
      ((CB _ _ (genericSourceSquare_coordinateBaseChange K alpha m n)).compact A.input (A.input_lisse CR)).hom ≫
        Abelian.factorThruImage (H'.comparison
          ((O.curve (specializationMorphism K alpha m n)).obj A.input)) :=
  fromCompact_parabolicBaseChangeIso (goodCohomology D (H := H)) H'
    (O.base (radialParameterMorphism K alpha m n))
    (fun A => (O.curve (specializationMorphism K alpha m n)).obj A.val)
    (genericGoodBaseChange K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n)
    ⟨A.input, input_good D CR A⟩

theorem genericParabolicBaseChangeIso_toOrdinary (A : KloostermanInputData D) :
    (genericParabolicBaseChangeIso K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n A).hom ≫
        Abelian.image.ι (H'.comparison ((O.curve (specializationMorphism K alpha m n)).obj A.input)) =
      (O.base (radialParameterMorphism K alpha m n)).map (Abelian.image.ι (H.comparison A.input)) ≫
        ((genericGoodBaseChange K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n).ordinary
          ⟨A.input, input_good D CR A⟩).hom :=
  parabolicBaseChangeIso_toOrdinary (goodCohomology D (H := H)) H'
    (O.base (radialParameterMorphism K alpha m n))
    (fun A => (O.curve (specializationMorphism K alpha m n)).obj A.val)
    (genericGoodBaseChange K D CR G DT S D' CR' G' DT' S' CF O CB PN alpha m n)
    ⟨A.input, input_good D CR A⟩

end PrimeGap182.TypeIII.GenericCohomologyBaseChange

#print axioms PrimeGap182.TypeIII.GenericCohomologyBaseChange.genericGoodBaseChange
#print axioms PrimeGap182.TypeIII.GenericCohomologyBaseChange.genericParabolicBaseChangeIso
#print axioms PrimeGap182.TypeIII.GenericCohomologyBaseChange.genericParabolicBaseChangeIso_fromCompact
#print axioms PrimeGap182.TypeIII.GenericCohomologyBaseChange.genericParabolicBaseChangeIso_toOrdinary
