import TypeIIIRationalPointStalks

/-!
# The actual source projection used by the common QST constructor

The source is the existing closed affine presentation of Gm cubed with
coordinates (x,xInv,lambda,lambdaInv,xi,xiInv). The actual projection to
the existing parameter torus retains lambda and xi and forgets x.
Its coordinate ring map is the existing universal torus evaluation at
source coordinateUnit 1 and coordinateUnit 2. The polynomial presentation
has the four literal source coordinates 2,3,4,5, each of degree one.
The composition with every original curvePoint is the original schemePoint.

This module proves only coordinate-ring and scheme-map identities and
their polynomial degrees. It supplies no QST theorem, sheaf model,
geometric embedding complexity, or complete Type III input family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.SourceProjectionForQST

universe u
variable (K : Type u) [Field K]

/-- Target torus coordinates map to the lambda and xi source coordinates. -/
def sourceIndex : Fin 4 → Fin 6 := ![2, 3, 4, 5]

def polynomials : Fin 4 → MvPolynomial (Fin 6) K :=
  fun i => X (sourceIndex i)

/-- The ACTUAL parameter projection on coordinate rings; unit0 remains
the source fiber coordinate x, while units 1 and 2 are retained. -/
def projectionHom : PhysicalTorusMorphism.TorusRing K →ₐ[K]
    StartingSourceMaps.SourceRing K :=
  PhysicalTorusMorphism.evaluation
    (StartingSourceMaps.coordinateUnit K 1) (StartingSourceMaps.coordinateUnit K 2)

def projection : StartingSourceMaps.sourceScheme K ⟶ PhysicalTorusMorphism.torusScheme K :=
  Spec.map (CommRingCat.ofHom (projectionHom K).toRingHom)

theorem projectionHom_coordinate (i : Fin 4) :
    projectionHom K (PhysicalTorusMorphism.coordinate K i) =
      StartingSourceMaps.coordinate K (sourceIndex i) := by
  rw [projectionHom, PhysicalTorusMorphism.evaluation_coordinate]
  fin_cases i <;> rfl

/-- The exact map on the fixed closed affine A6/A4 presentations. -/
theorem projectionHom_polynomial_presentation :
    (projectionHom K).comp (PhysicalTorusMorphism.quotient K) =
      aeval (fun i => StartingSourceMaps.quotient K (polynomials K i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, aeval_X, PhysicalTorusMorphism.coordinate,
    StartingSourceMaps.coordinate, polynomials] using projectionHom_coordinate K i

theorem polynomials_degree_le (i : Fin 4) : (polynomials K i).totalDegree ≤ 1 := by
  simp [polynomials]

variable {K} {A : Type u} [CommRing A] [Algebra K A]

/-- Evaluation over EVERY coefficient algebra recovers the same two
parameter units, independently of the unit x in the source fiber. -/
theorem evaluation_comp_projectionHom (x lambda xi : Aˣ) :
    (StartingSourceMaps.evaluation (K := K) x lambda xi).comp (projectionHom K) =
      PhysicalTorusMorphism.evaluation lambda xi := by
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  change StartingSourceMaps.evaluation x lambda xi
      (projectionHom K (PhysicalTorusMorphism.coordinate K i)) =
    PhysicalTorusMorphism.evaluation lambda xi (PhysicalTorusMorphism.coordinate K i)
  rw [projectionHom_coordinate, StartingSourceMaps.evaluation_coordinate,
    PhysicalTorusMorphism.evaluation_coordinate]
  fin_cases i <;> rfl

/-- The actual source point over an arbitrary coefficient algebra. -/
def algebraPoint (x lambda xi : Aˣ) : Spec (.of A) ⟶ StartingSourceMaps.sourceScheme K :=
  Spec.map (CommRingCat.ofHom (StartingSourceMaps.evaluation (K := K) x lambda xi).toRingHom)

theorem algebraPoint_projection (x lambda xi : Aˣ) :
    algebraPoint x lambda xi ≫ projection K = PhysicalTorusMorphism.schemePoint lambda xi := by
  dsimp only [algebraPoint, projection, PhysicalTorusMorphism.schemePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (evaluation_comp_projectionHom x lambda xi))

/-- The original curvePoint, with its original three units, lies over
the original parameter schemePoint after the actual projection. -/
theorem curvePoint_projection (K0 : Type) [Field K0]
    {L : Type} [Field L] [Algebra K0 L] (x lambda xi : Lˣ) :
    RationalPointStalks.curvePoint (K := K0) x lambda xi ≫ projection K0 =
      PhysicalTorusMorphism.schemePoint lambda xi :=
  algebraPoint_projection x lambda xi

end PrimeGap182.TypeIII.SourceProjectionForQST

#print axioms PrimeGap182.TypeIII.SourceProjectionForQST.projectionHom_coordinate
#print axioms PrimeGap182.TypeIII.SourceProjectionForQST.projectionHom_polynomial_presentation
#print axioms PrimeGap182.TypeIII.SourceProjectionForQST.polynomials_degree_le
#print axioms PrimeGap182.TypeIII.SourceProjectionForQST.evaluation_comp_projectionHom
#print axioms PrimeGap182.TypeIII.SourceProjectionForQST.algebraPoint_projection
#print axioms PrimeGap182.TypeIII.SourceProjectionForQST.curvePoint_projection
