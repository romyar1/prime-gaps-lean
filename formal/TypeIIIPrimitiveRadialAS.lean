import TypeIIIPrimitiveLinearAS
import TypeIIIFuFromQuadraticPullback

/-!
# Radial pole characters from the original Artin–Schreier source

The rank-one models used in the quadratic-cover formula are constructed
by pulling back the same primitive AS object along beta/T and applying
radial wild inertia. Their general profile, rank and phase laws remain
published inputs. No independent family of rank-one representations is
supplied, and no existence of the common sheaf realization is asserted.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace PrimeGap182.TypeIII.PrimitiveRadialAS

open StartingSourceMaps PublishedPhaseApplication FourierSourceMaps
open FuFromQuadraticPullback

universe u v w a b c d t
variable (K : Type u) [Field K]

/-- The actual pole map to A1, also defined at coefficient zero. -/
def poleHom (beta : PhaseField K) : MvPolynomial (Fin 1) K →ₐ[K] LocalRing K :=
  aeval (fun _ => LaurentPolynomial.C beta * LaurentPolynomial.T (-1))

/-- Invert the punctured-line coordinate, fixing the coefficient field. -/
def inversionHom : LocalRing K →ₐ[K] LocalRing K where
  toRingHom := LaurentPolynomial.eval₂ LaurentPolynomial.C
    (PhysicalTorusLaurent.variableUnit (PhaseField K))⁻¹
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap K (PhaseField K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    rfl

/-- The radial character uses the inverse-coordinate pullback of the
linear character constructed from the original primitive source. -/
theorem poleHom_inversion (beta : PhaseField K) :
    poleHom K beta = (inversionHom K).comp (PrimitiveLinearAS.linearHom K beta) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [poleHom, PrimitiveLinearAS.linearHom, AlgHom.comp_apply, aeval_X]
  change _ = LaurentPolynomial.eval₂ LaurentPolynomial.C _
    (LaurentPolynomial.C beta * LaurentPolynomial.T 1)
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_one]
  rfl

/-- Under T ↦ r*T the pole coefficient is divided by r. -/
theorem poleHom_scalar_comp (beta : PhaseField K) (r : (PhaseField K)ˣ) :
    (scalarHom K r).comp (poleHom K beta) = poleHom K (beta / (r : PhaseField K)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, poleHom, aeval_X]
  change LaurentPolynomial.eval₂ LaurentPolynomial.C _
    (LaurentPolynomial.C beta * LaurentPolynomial.T (-1)) = _
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_neg_one,
    mul_inv_rev]
  change LaurentPolynomial.C beta *
    (LaurentPolynomial.T (-1) * LaurentPolynomial.C ((r⁻¹ : (PhaseField K)ˣ) : PhaseField K)) = _
  rw [Units.val_inv_eq_inv_val, div_eq_mul_inv, map_mul]
  ring

def poleMorphism (beta : PhaseField K) : localScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (poleHom K beta).toRingHom)

def inversionMorphism : localScheme K ⟶ localScheme K :=
  Spec.map (CommRingCat.ofHom (inversionHom K).toRingHom)

theorem poleMorphism_inversion (beta : PhaseField K) :
    poleMorphism K beta = inversionMorphism K ≫ PrimitiveLinearAS.linearMorphism K beta := by
  dsimp only [poleMorphism, inversionMorphism, PrimitiveLinearAS.linearMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (congrArg AlgHom.toRingHom (poleHom_inversion K beta))

variable {Line : Type v} [Category.{a} Line]
  {Local : Type w} [Category.{b} Local]
  {E : Type c} [Field E] {G : Type d} [Group G]

def phase (restriction : (localScheme K ⟶ affineLine K) → Line ⥤ Local)
    (inertia : Local ⥤ FDRep E G) (as : Line) (beta : PhaseField K) : FDRep E G :=
  inertia.obj ((restriction (poleMorphism K beta)).obj as)

/-- General AS character laws for the constructed pole representations.
At beta=0 this is a trivial rank-one character, not the zero object. -/
structure PhaseLaws (D : PhaseData K E G)
    (restriction : (localScheme K ⟶ affineLine K) → Line ⥤ Local)
    (inertia : Local ⥤ FDRep E G) (as : Line) where
  profile : ∀ beta, D.HasProfile (phase K restriction inertia as beta)
  rank : ∀ beta, Module.finrank E (phase K restriction inertia as beta) = 1
  phases : ∀ beta, D.phases (phase K restriction inertia as beta) = {beta}

def models (D : PhaseData K E G)
    (restriction : (localScheme K ⟶ affineLine K) → Line ⥤ Local)
    (inertia : Local ⥤ FDRep E G) (as : Line)
    (laws : PhaseLaws K D restriction inertia as) : LinearPhaseModels D where
  phase := phase K restriction inertia as
  profile := laws.profile
  rank := laws.rank
  phases := laws.phases

/-- Published geometric inputs on one primitive AS source. The covering
comparison is required for the constructed radial characters. -/
structure Inputs [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : PhaseData K E G) (C : CubicFourierData K E G)
    (restriction : (localScheme K ⟶ affineLine K) → Line ⥤ Local) (as : Line) where
  inertia : Local ⥤ FDRep E G
  laws : PhaseLaws K D restriction inertia as
  Twist : Type t
  quadratic : QuadraticData (K := K) (E := E) (G := G) Twist
  coverRules : QuadraticRules p (models K D restriction inertia as laws) quadratic
  comparison : FuComparison p C quadratic

/-- Feed the constructed phase family to the existing checked Fu application. -/
def Inputs.fourierInputs [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    {D : PhaseData K E G} {C : CubicFourierData K E G}
    {restriction : (localScheme K ⟶ affineLine K) → Line ⥤ Local} {as : Line}
    (S : Inputs K p D C restriction as) : FuFromQuadraticPullback.Inputs p D C where
  Twist := S.Twist
  linear := models K D restriction S.inertia as S.laws
  quadratic := S.quadratic
  coverRules := S.coverRules
  comparison := S.comparison

end PrimeGap182.TypeIII.PrimitiveRadialAS

#print axioms PrimeGap182.TypeIII.PrimitiveRadialAS.poleHom_inversion
#print axioms PrimeGap182.TypeIII.PrimitiveRadialAS.poleHom_scalar_comp
#print axioms PrimeGap182.TypeIII.PrimitiveRadialAS.poleMorphism_inversion
#print axioms PrimeGap182.TypeIII.PrimitiveRadialAS.phase
#print axioms PrimeGap182.TypeIII.PrimitiveRadialAS.models
#print axioms PrimeGap182.TypeIII.PrimitiveRadialAS.Inputs.fourierInputs
