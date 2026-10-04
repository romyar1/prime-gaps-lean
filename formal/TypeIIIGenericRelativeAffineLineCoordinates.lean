import TypeIIIGenericCurvePullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Actual relative affine-line ambient for the generic punctured curve

The generic curve is Laurent in x over the ORIGINAL parameter ring. Its
actual relative A1 ambient is polynomial in x over that SAME ring. The open
map is the Laurent localization, using the existing unique-variable
polynomial equivalence and localization-away-X theorem. Its projection
composition is the original genericProjection. The actual zero section
splits this projection. No P1 compactification, cohomology operation,
support model or published theorem capability is assumed by this leaf.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.GenericRelativeAffineLineCoordinates
open GenericCurvePullback GenericSourceSpecialization SourceCurveBaseChange

variable (K : Type) [Field K]

abbrev RelativeAffineRing := MvPolynomial (Fin 1) (ParameterRing K)
abbrev relativeAffineScheme : Scheme := Spec (.of (RelativeAffineRing K))

/-- The actual x-polynomial inclusion into the existing generic Laurent ring. -/
def relativeOpenHom : RelativeAffineRing K →+* GenericRing K :=
  Polynomial.toLaurent.comp (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingHom

theorem relativeOpenHom_C (a : ParameterRing K) :
    relativeOpenHom K (MvPolynomial.C a) = LaurentPolynomial.C a := by
  change Polynomial.toLaurent
    ((MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)) (MvPolynomial.C a)) = _
  change Polynomial.toLaurent (MvPolynomial.eval₂ Polynomial.C
    (fun _ => Polynomial.X) (MvPolynomial.C a)) = _
  rw [MvPolynomial.eval₂_C, Polynomial.toLaurent_C]

theorem relativeOpenHom_X (i : Fin 1) :
    relativeOpenHom K (MvPolynomial.X i) = (curveUnit K : GenericRing K) := by
  change Polynomial.toLaurent
    ((MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)) (MvPolynomial.X i)) = _
  change Polynomial.toLaurent (MvPolynomial.eval₂ Polynomial.C
    (fun _ => Polynomial.X) (MvPolynomial.X i)) = _
  rw [MvPolynomial.eval₂_X, Polynomial.toLaurent_X]
  rfl

def relativeOpenMorphism : genericScheme K ⟶ relativeAffineScheme K :=
  Spec.map (CommRingCat.ofHom (relativeOpenHom K))

/-- Genuine open immersion, derived from the actual Away-X localization. -/
instance relativeOpenMorphism_isOpenImmersion : IsOpenImmersion (relativeOpenMorphism K) := by
  dsimp only [relativeOpenMorphism, relativeOpenHom]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial (ParameterRing K) →+* GenericRing K))) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial (ParameterRing K)) (GenericRing K))))
    exact IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial (ParameterRing K))
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingHom) :=
    inferInstanceAs (IsIso
      (MvPolynomial.uniqueAlgEquiv (ParameterRing K) (Fin 1)).toRingEquiv.toCommRingCatIso.hom)
  infer_instance

def relativeProjection : relativeAffineScheme K ⟶ parameterScheme K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K))

theorem relativeOpenHom_comp_C :
    (relativeOpenHom K).comp (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K) =
      (coefficientHom K (A := ParameterRing K)).toRingHom := by
  apply RingHom.ext
  intro a
  exact relativeOpenHom_C K a

/-- The generic projection is exactly the open embedding followed by A1 projection. -/
theorem relativeOpen_comp_projection :
    relativeOpenMorphism K ≫ relativeProjection K = genericProjection K := by
  dsimp only [relativeOpenMorphism, relativeProjection, genericProjection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, relativeOpenHom_comp_C]

def relativeZeroHom : RelativeAffineRing K →+* ParameterRing K :=
  MvPolynomial.eval₂Hom (RingHom.id _) (fun _ => 0)

def relativeZeroSection : parameterScheme K ⟶ relativeAffineScheme K :=
  Spec.map (CommRingCat.ofHom (relativeZeroHom K))

/-- Zero is an actual section over the SAME original parameter scheme. -/
theorem relativeZeroSection_comp_projection :
    relativeZeroSection K ≫ relativeProjection K = 𝟙 (parameterScheme K) := by
  dsimp only [relativeZeroSection, relativeProjection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (relativeZeroHom K).comp
      (MvPolynomial.C : ParameterRing K →+* RelativeAffineRing K) = RingHom.id _ := by
    apply RingHom.ext
    intro a
    exact MvPolynomial.eval₂_C _ _ a
  rw [h]
  exact Spec.map_id _

end PrimeGap182.TypeIII.GenericRelativeAffineLineCoordinates
