import TypeIIIOriginPoleFromExactInverseImages
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual squared radial coordinates at the generic plane point

The SAME canonical transcendental direction and radial map are used.
Positive powers of the Laurent-series uniformizer give injective maps
from the full-plane coordinate ring. Exponent two is exactly the frozen
radial map, with a factorization through its actual punctured origin.
No perverse, ordinary-cohomology, generic-stalk or wild exactness law is
assumed or proved by this coordinate application.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.RadialGenericDominance
open PublishedPhaseApplication LinearRadialPhaseFromPoleTransport

variable (k : Type) [Field k]

def exponentShear : (Fin 2 →₀ ℕ) →+ (Fin 2 →₀ ℕ) where
  toFun m := Finsupp.single 0 (m 0 + m 1) + Finsupp.single 1 (m 1)
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' m n := by ext i; fin_cases i <;> simp [add_left_comm, add_comm]

theorem exponentShear_injective : Function.Injective exponentShear := by
  intro m n h
  have h0 := congrArg (fun p : Fin 2 →₀ ℕ => p 0) h
  have h1 := congrArg (fun p : Fin 2 →₀ ℕ => p 1) h
  simp [exponentShear] at h0 h1
  ext i
  fin_cases i
  · change m 0 = n 0
    omega
  · change m 1 = n 1
    exact h1

def shearHom : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k exponentShear

theorem shearHom_injective : Function.Injective (shearHom k) :=
  AddMonoidAlgebra.mapDomain_injective exponentShear_injective

@[simp] theorem shearHom_X_zero : shearHom k (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  change AddMonoidAlgebra.mapDomain exponentShear
    (AddMonoidAlgebra.single (Finsupp.single 0 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  simp [exponentShear, MvPolynomial.X, ← MvPolynomial.single_eq_monomial]

@[simp] theorem shearHom_X_one :
    shearHom k (MvPolynomial.X 1) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  change AddMonoidAlgebra.mapDomain exponentShear
    (AddMonoidAlgebra.single (Finsupp.single 1 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  simp [exponentShear, MvPolynomial.X, ← MvPolynomial.single_eq_monomial,
    AddMonoidAlgebra.single_mul_single]

theorem direction_transcendental : Transcendental k (direction k) := by
  exact (transcendental_algebraMap_iff
    (algebraMap (RatFunc k) (PhaseField k)).injective).2 RatFunc.transcendental_X

def directionHom : MvPolynomial (Fin 1) k →ₐ[k] PhaseField k :=
  MvPolynomial.aeval (fun _ => direction k)

theorem directionHom_injective : Function.Injective (directionHom k) := by
  have h : AlgebraicIndependent k (fun _ : Fin 1 => direction k) :=
    algebraicIndependent_unique_type_iff.mpr (direction_transcendental k)
  exact algebraicIndependent_iff_injective_aeval.mp h

def genericLineHom : MvPolynomial (Fin 2) k →ₐ[k] Polynomial (PhaseField k) :=
  (Polynomial.mapAlgHom (directionHom k)).comp (MvPolynomial.finSuccEquiv k 1).toAlgHom

theorem genericLineHom_injective : Function.Injective (genericLineHom k) :=
  (Polynomial.map_injective _ (directionHom_injective k)).comp
    (MvPolynomial.finSuccEquiv k 1).injective

def radialPolynomialHom (d : ℕ) : MvPolynomial (Fin 2) k →ₐ[k] Polynomial (PhaseField k) :=
  MvPolynomial.aeval (fun i =>
    if i = 0 then Polynomial.X ^ d else Polynomial.C (direction k) * Polynomial.X ^ d)

theorem radialPolynomialHom_one :
    radialPolynomialHom k 1 = (genericLineHom k).comp (shearHom k) := by
  apply MvPolynomial.algHom_ext
  intro i
  have h1 : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := k) (j := (0 : Fin 1))
  fin_cases i <;>
    simp [radialPolynomialHom, genericLineHom, directionHom,
      MvPolynomial.finSuccEquiv_X_zero, h1]

theorem radialPolynomialHom_expand (d : ℕ) :
    radialPolynomialHom k d = ((Polynomial.expand (PhaseField k) d).restrictScalars k).comp
      (radialPolynomialHom k 1) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [radialPolynomialHom]

theorem radialPolynomialHom_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (radialPolynomialHom k d) := by
  rw [radialPolynomialHom_expand, radialPolynomialHom_one]
  exact (Polynomial.expand_injective hd).comp
    ((genericLineHom_injective k).comp (shearHom_injective k))

theorem radialPolynomialHom_two : radialPolynomialHom k 2 = radialHom (k := k) := rfl

abbrev genericScheme : Scheme := Spec (.of (LaurentSeries (PhaseField k)))

def polynomialSeriesHom : Polynomial (PhaseField k) →+* LaurentSeries (PhaseField k) :=
  algebraMap _ _

def uniformizer : LaurentSeries (PhaseField k) := polynomialSeriesHom k Polynomial.X

theorem uniformizer_eq_single : uniformizer k = HahnSeries.single 1 1 := by
  simp [uniformizer, polynomialSeriesHom]

theorem coefficientSeries (c : PhaseField k) :
    algebraMap (PhaseField k) (LaurentSeries (PhaseField k)) c = HahnSeries.C c := by
  simp [HahnSeries.algebraMap_apply']

theorem uniformizer_ne_zero : uniformizer k ≠ 0 := by
  have h := Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := PhaseField k)
  simpa only [uniformizer, polynomialSeriesHom, map_zero] using h.ne Polynomial.X_ne_zero

def radialSeriesHom (d : ℕ) : MvPolynomial (Fin 2) k →+* LaurentSeries (PhaseField k) :=
  (polynomialSeriesHom k).comp (radialPolynomialHom k d).toRingHom

theorem radialSeriesHom_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (radialSeriesHom k d) :=
  (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ)).comp
    (radialPolynomialHom_injective k d hd)

@[simp] theorem radialSeriesHom_X (d : ℕ) (i : Fin 2) :
    radialSeriesHom k d (MvPolynomial.X i) =
      if i = 0 then uniformizer k ^ d else
        algebraMap (PhaseField k) (LaurentSeries (PhaseField k)) (direction k) * uniformizer k ^ d := by
  fin_cases i <;> simp [radialSeriesHom, radialPolynomialHom, uniformizer,
    polynomialSeriesHom, coefficientSeries, HahnSeries.C,
    HahnSeries.single_mul_single]

def radialSeriesMorphism (d : ℕ) : genericScheme k ⟶ FullFourierKernelCoordinates.planeScheme k :=
  Spec.map (CommRingCat.ofHom (radialSeriesHom k d))

theorem radialSeriesMorphism_isDominant (d : ℕ) (hd : 0 < d) :
    IsDominant (radialSeriesMorphism k d) := by
  apply isDominant_of_of_appTop_injective
  let R : CommRingCat := .of (MvPolynomial (Fin 2) k)
  let S : CommRingCat := .of (LaurentSeries (PhaseField k))
  let f : R ⟶ S := CommRingCat.ofHom (radialSeriesHom k d)
  change Function.Injective (Spec.map f).appTop
  have h : (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
    calc
      (Spec.map f).appTop =
          ((Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom) ≫ (Scheme.ΓSpecIso S).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = ((Scheme.ΓSpecIso R).hom ≫ f) ≫ (Scheme.ΓSpecIso S).inv :=
        congrArg (fun g => g ≫ (Scheme.ΓSpecIso S).inv) (Scheme.ΓSpecIso_naturality f)
      _ = _ := Category.assoc ..
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1.comp
    ((radialSeriesHom_injective k d hd).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)

def seriesOriginMorphism : genericScheme k ⟶ originScheme k :=
  Spec.map (CommRingCat.ofHom (polynomialSeriesHom k))

theorem seriesOrigin_radialMorphism :
    seriesOriginMorphism k ≫ radialMorphism (k := k) = radialSeriesMorphism k 2 := by
  dsimp only [seriesOriginMorphism, radialMorphism, radialSeriesMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

def seriesTraitHom : LaurentPolynomial (PhaseField k) →+* LaurentSeries (PhaseField k) :=
  LaurentPolynomial.eval₂ (algebraMap _ _) (Units.mk0 (uniformizer k) (uniformizer_ne_zero k))

theorem seriesTraitHom_toLaurent :
    (seriesTraitHom k).comp Polynomial.toLaurent = polynomialSeriesHom k := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [seriesTraitHom, polynomialSeriesHom, coefficientSeries, HahnSeries.C]
  · simp [seriesTraitHom, uniformizer]

def seriesTraitMorphism : genericScheme k ⟶ FourierSourceMaps.localScheme k :=
  Spec.map (CommRingCat.ofHom (seriesTraitHom k))

theorem seriesTrait_puncturedOpen :
    seriesTraitMorphism k ≫ OriginPoleFromExactInverseImages.puncturedOpen k =
      seriesOriginMorphism k := by
  dsimp only [seriesTraitMorphism, OriginPoleFromExactInverseImages.puncturedOpen,
    seriesOriginMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, seriesTraitHom_toLaurent]

theorem seriesTrait_radialMorphism :
    seriesTraitMorphism k ≫ OriginPoleFromExactInverseImages.puncturedOpen k ≫
      radialMorphism (k := k) = radialSeriesMorphism k 2 := by
  rw [← Category.assoc, seriesTrait_puncturedOpen, seriesOrigin_radialMorphism]

end PrimeGap182.TypeIII.RadialGenericDominance

#print axioms PrimeGap182.TypeIII.RadialGenericDominance.radialSeriesHom_injective
#print axioms PrimeGap182.TypeIII.RadialGenericDominance.seriesOrigin_radialMorphism
#print axioms PrimeGap182.TypeIII.RadialGenericDominance.seriesTrait_puncturedOpen
#print axioms PrimeGap182.TypeIII.RadialGenericDominance.radialSeriesMorphism_isDominant
