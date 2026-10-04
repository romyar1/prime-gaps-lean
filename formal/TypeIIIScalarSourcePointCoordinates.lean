import TypeIIISourceProjectionForQST
import TypeIIICanonicalCurveInput

/-!
# Actual scalar source maps at unit points

The original scalar map evaluates at the product of the source unit x and
the original parameter-ring unit evaluated at (lambda,xi). These are
coordinate-ring and Spec identities for every coefficient algebra; the
original finite-field curvePoint and linePoint APIs are specializations.
No stalk, rank-constancy, sheaf realization or new mathematical law is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.ScalarSourcePointCoordinates

universe u
variable (K : Type u) [Field K]
variable {A : Type u} [CommRing A] [Algebra K A]

/-- The actual image is a unit, with the original coefficient evaluated
on the two parameter units before multiplication by the source unit. -/
def scalarPointValue (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (x lambda xi : Aˣ) : Aˣ :=
  x * Units.map (PhysicalTorusMorphism.evaluation (K := K) lambda xi).toRingHom c

theorem scalarPointValue_ne_zero [Nontrivial A]
    (c : (PhysicalTorusMorphism.TorusRing K)ˣ) (x lambda xi : Aˣ) :
    (scalarPointValue K c x lambda xi : A) ≠ 0 :=
  Units.ne_zero _

theorem evaluation_parameterHom (x lambda xi : Aˣ) :
    (StartingSourceMaps.evaluation (K := K) x lambda xi).comp
      (CanonicalCurveInput.parameterHom K) =
      PhysicalTorusMorphism.evaluation (K := K) lambda xi :=
  SourceProjectionForQST.evaluation_comp_projectionHom x lambda xi

theorem evaluation_scalarHom_X (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (x lambda xi : Aˣ) :
    StartingSourceMaps.evaluation (K := K) x lambda xi
      (CanonicalCurveInput.scalarHom K c (X 0)) =
      (scalarPointValue K c x lambda xi : A) := by
  have hp := DFunLike.congr_fun (evaluation_parameterHom K x lambda xi) (c : PhysicalTorusMorphism.TorusRing K)
  simp only [AlgHom.comp_apply] at hp
  have hx : StartingSourceMaps.evaluation (K := K) x lambda xi
      (StartingSourceMaps.coordinateUnit K 0 : StartingSourceMaps.SourceRing K) =
      (x : A) := by
    exact StartingSourceMaps.evaluation_coordinate x lambda xi 0
  rw [CanonicalCurveInput.scalarHom, aeval_X]
  change StartingSourceMaps.evaluation x lambda xi
      ((CanonicalCurveInput.parameterHom K (c : _)) *
        (StartingSourceMaps.coordinateUnit K 0 : StartingSourceMaps.SourceRing K)) = _
  rw [map_mul, hp, hx]
  exact mul_comm _ _

theorem evaluation_comp_scalarHom (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (x lambda xi : Aˣ) :
    (StartingSourceMaps.evaluation (K := K) x lambda xi).comp
      (CanonicalCurveInput.scalarHom K c) =
      aeval (fun _ : Fin 1 => (scalarPointValue K c x lambda xi : A)) := by
  apply MvPolynomial.algHom_ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  simp only [AlgHom.comp_apply, aeval_X]
  exact evaluation_scalarHom_X K c x lambda xi

/-- A line point over an arbitrary coefficient algebra. -/
def algebraLinePoint (z : A) : Spec (.of A) ⟶ StartingSourceMaps.affineLine K :=
  Spec.map (CommRingCat.ofHom (aeval (R := K) (fun _ : Fin 1 => z)).toRingHom)

theorem algebraPoint_scalarMorphism (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (x lambda xi : Aˣ) :
    SourceProjectionForQST.algebraPoint (K := K) x lambda xi ≫
      CanonicalCurveInput.scalarMorphism K c =
      algebraLinePoint K (scalarPointValue K c x lambda xi : A) := by
  dsimp only [SourceProjectionForQST.algebraPoint, CanonicalCurveInput.scalarMorphism,
    algebraLinePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (evaluation_comp_scalarHom K c x lambda xi))

theorem scalarPointValue_one (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    scalarPointValue K c (1 : Aˣ) 1 1 =
      Units.map (PhysicalTorusMorphism.evaluation (K := K) (1 : Aˣ) 1).toRingHom c :=
  one_mul _

theorem algebraPoint_one_scalarMorphism (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    SourceProjectionForQST.algebraPoint (K := K) (1 : Aˣ) 1 1 ≫
      CanonicalCurveInput.scalarMorphism K c =
      algebraLinePoint K
        ((Units.map (PhysicalTorusMorphism.evaluation (K := K) (1 : Aˣ) 1).toRingHom c : Aˣ) : A) := by
  simpa only [scalarPointValue_one] using algebraPoint_scalarMorphism K c (1 : Aˣ) 1 1

section OriginalPoints

variable {K0 : Type} [Field K0] {E : Type} [Field E] [Algebra K0 E]

/-- The exact original point-map equation, with no finiteness restriction. -/
theorem curvePoint_scalarMorphism (c : (PhysicalTorusMorphism.TorusRing K0)ˣ)
    (x lambda xi : Eˣ) :
    RationalPointStalks.curvePoint (K := K0) x lambda xi ≫
      CanonicalCurveInput.scalarMorphism K0 c =
      RationalPointStalks.linePoint (K := K0)
        (scalarPointValue K0 c x lambda xi : E) :=
  algebraPoint_scalarMorphism K0 c x lambda xi

theorem curvePoint_one_scalarMorphism (c : (PhysicalTorusMorphism.TorusRing K0)ˣ) :
    RationalPointStalks.curvePoint (K := K0) (1 : Eˣ) 1 1 ≫
      CanonicalCurveInput.scalarMorphism K0 c =
      RationalPointStalks.linePoint (K := K0)
        ((Units.map (PhysicalTorusMorphism.evaluation (K := K0) (1 : Eˣ) 1).toRingHom c : Eˣ) : E) :=
  algebraPoint_one_scalarMorphism K0 c

end OriginalPoints
end PrimeGap182.TypeIII.ScalarSourcePointCoordinates
