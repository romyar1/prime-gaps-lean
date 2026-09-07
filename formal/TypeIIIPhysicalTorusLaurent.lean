import TypeIIIPhysicalTorusMorphism
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The physical torus coordinate ring is a Laurent polynomial ring

This identifies the literal quotient K[x,xInv,y,yInv]/(x*xInv-1,y*yInv-1)
with the iterated Laurent polynomial K-algebra.  The equivalence is
constructed from the universal evaluations at actual units, in both
directions.  Thus the closed affine presentation used for quantitative
sheaf theory is an integral, reduced torus scheme, independently of any
argument involving rational points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.PhysicalTorusLaurent

open PhysicalTorusMorphism

universe u

/-- The unit defined by the Laurent indeterminate. -/
def variableUnit (R : Type u) [CommRing R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

theorem variableUnit_pow (R : Type u) [CommRing R] (n : ℤ) :
    ((variableUnit R ^ n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) =
      LaurentPolynomial.T n := by
  cases n with
  | ofNat n => simp [variableUnit, LaurentPolynomial.T_pow]
  | negSucc n =>
    rw [zpow_negSucc]
    simp only [← inv_pow, Units.val_pow_eq_pow_val]
    change LaurentPolynomial.T (-1) ^ (n + 1) = (LaurentPolynomial.T _ : LaurentPolynomial R)
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega

variable (K : Type u) [Field K]

/-- The two-variable Laurent polynomial K-algebra, with x the inner
variable and y the outer variable. -/
abbrev DoubleLaurent := LaurentPolynomial (LaurentPolynomial K)

def laurentX : (DoubleLaurent K)ˣ :=
  Units.map (LaurentPolynomial.C : LaurentPolynomial K →+* DoubleLaurent K).toMonoidHom
    (variableUnit K)

def laurentY : (DoubleLaurent K)ˣ := variableUnit (LaurentPolynomial K)

/-- Forward evaluation of the original quotient at the Laurent units. -/
def toLaurent : TorusRing K →ₐ[K] DoubleLaurent K :=
  evaluation (laurentX K) (laurentY K)

/-- Evaluation of the inner Laurent polynomial variable at x. -/
def innerEvaluation : LaurentPolynomial K →+* TorusRing K :=
  LaurentPolynomial.eval₂ (algebraMap K (TorusRing K)) (xUnit K)

/-- Reverse evaluation sends the two Laurent variables to the two
literal units in the original quotient ring. -/
def fromLaurent : DoubleLaurent K →ₐ[K] TorusRing K where
  toRingHom := LaurentPolynomial.eval₂ (innerEvaluation K) (yUnit K)
  commutes' c := by
    change LaurentPolynomial.eval₂ (innerEvaluation K) (yUnit K)
      (LaurentPolynomial.C (LaurentPolynomial.C c)) = algebraMap K (TorusRing K) c
    rw [LaurentPolynomial.eval₂_C]
    exact LaurentPolynomial.eval₂_C _ _ c

theorem fromLaurent_C (a : LaurentPolynomial K) :
    fromLaurent K (LaurentPolynomial.C a) = innerEvaluation K a :=
  LaurentPolynomial.eval₂_C _ _ a

theorem fromLaurent_T (n : ℤ) :
    fromLaurent K (LaurentPolynomial.T n) = ((yUnit K ^ n : (TorusRing K)ˣ) : TorusRing K) :=
  LaurentPolynomial.eval₂_T _ _ n

theorem innerEvaluation_C (c : K) :
    innerEvaluation K (LaurentPolynomial.C c) = algebraMap K (TorusRing K) c :=
  LaurentPolynomial.eval₂_C _ _ c

theorem innerEvaluation_T (n : ℤ) :
    innerEvaluation K (LaurentPolynomial.T n) =
      ((xUnit K ^ n : (TorusRing K)ˣ) : TorusRing K) :=
  LaurentPolynomial.eval₂_T _ _ n

/-- Universal torus evaluation commutes with every coefficient-algebra
homomorphism, including maps to rings with nilpotents. -/
theorem evaluation_natural {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) (x y : Aˣ) :
    f.comp (evaluation (K := K) x y) =
      evaluation (Units.map f.toRingHom.toMonoidHom x)
        (Units.map f.toRingHom.toMonoidHom y) := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change f (evaluation (K := K) x y (coordinate K i)) =
    evaluation (Units.map f.toRingHom.toMonoidHom x)
      (Units.map f.toRingHom.toMonoidHom y) (coordinate K i)
  rw [evaluation_coordinate, evaluation_coordinate]
  fin_cases i <;> rfl

theorem evaluation_identity :
    evaluation (xUnit K) (yUnit K) = AlgHom.id K (TorusRing K) := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change evaluation (xUnit K) (yUnit K) (coordinate K i) = coordinate K i
  rw [evaluation_coordinate]
  fin_cases i <;> rfl

theorem map_fromLaurent_laurentX :
    Units.map (fromLaurent K).toRingHom.toMonoidHom (laurentX K) = xUnit K := by
  apply Units.ext
  change fromLaurent K (LaurentPolynomial.C (LaurentPolynomial.T 1)) = coordinate K 0
  rw [fromLaurent_C, innerEvaluation_T]
  simp only [zpow_one]
  rfl

theorem map_fromLaurent_laurentY :
    Units.map (fromLaurent K).toRingHom.toMonoidHom (laurentY K) = yUnit K := by
  apply Units.ext
  change fromLaurent K (LaurentPolynomial.T 1) = coordinate K 2
  rw [fromLaurent_T]
  simp only [zpow_one]
  rfl

/-- The original quotient is recovered on all ring elements. -/
theorem fromLaurent_comp_toLaurent :
    (fromLaurent K).comp (toLaurent K) = AlgHom.id K (TorusRing K) := by
  rw [toLaurent, evaluation_natural, map_fromLaurent_laurentX,
    map_fromLaurent_laurentY, evaluation_identity]

theorem map_toLaurent_xUnit :
    Units.map (toLaurent K).toRingHom.toMonoidHom (xUnit K) = laurentX K :=
  map_evaluation_xUnit (laurentX K) (laurentY K)

theorem map_toLaurent_yUnit :
    Units.map (toLaurent K).toRingHom.toMonoidHom (yUnit K) = laurentY K :=
  map_evaluation_yUnit (laurentX K) (laurentY K)

theorem laurentX_pow (n : ℤ) :
    ((laurentX K ^ n : (DoubleLaurent K)ˣ) : DoubleLaurent K) =
      LaurentPolynomial.C (LaurentPolynomial.T n) := by
  change (((Units.map (LaurentPolynomial.C : LaurentPolynomial K →+* DoubleLaurent K).toMonoidHom
    (variableUnit K)) ^ n : (DoubleLaurent K)ˣ) : DoubleLaurent K) = _
  rw [← map_zpow]
  change LaurentPolynomial.C ((variableUnit K ^ n : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = _
  rw [variableUnit_pow]

theorem laurentY_pow (n : ℤ) :
    ((laurentY K ^ n : (DoubleLaurent K)ˣ) : DoubleLaurent K) =
      LaurentPolynomial.T n := variableUnit_pow (LaurentPolynomial K) n

theorem toLaurent_xUnit_pow (n : ℤ) :
    toLaurent K ((xUnit K ^ n : (TorusRing K)ˣ) : TorusRing K) =
      LaurentPolynomial.C (LaurentPolynomial.T n) := by
  change ((Units.map (toLaurent K).toRingHom.toMonoidHom (xUnit K ^ n) :
    (DoubleLaurent K)ˣ) : DoubleLaurent K) = _
  rw [map_zpow, map_toLaurent_xUnit, laurentX_pow]

theorem toLaurent_yUnit_pow (n : ℤ) :
    toLaurent K ((yUnit K ^ n : (TorusRing K)ˣ) : TorusRing K) =
      LaurentPolynomial.T n := by
  change ((Units.map (toLaurent K).toRingHom.toMonoidHom (yUnit K ^ n) :
    (DoubleLaurent K)ˣ) : DoubleLaurent K) = _
  rw [map_zpow, map_toLaurent_yUnit, laurentY_pow]

/-- The inner-variable inverse identity is proved on all Laurent monomials. -/
theorem toLaurent_innerEvaluation (a : LaurentPolynomial K) :
    toLaurent K (innerEvaluation K a) = LaurentPolynomial.C a := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | C_mul_T n c =>
    rw [map_mul, map_mul, map_mul, innerEvaluation_C, innerEvaluation_T,
      toLaurent_xUnit_pow, AlgHom.commutes]
    rfl

/-- The outer-variable inverse identity, again on all ring elements. -/
theorem toLaurent_fromLaurent (a : DoubleLaurent K) :
    toLaurent K (fromLaurent K a) = a := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | C_mul_T n c =>
    rw [map_mul, map_mul, fromLaurent_C, fromLaurent_T,
      toLaurent_yUnit_pow, toLaurent_innerEvaluation]

/-- The literal quotient ring is the two-variable Laurent polynomial
K-algebra.  This establishes its scheme-theoretic identity, not just a
bijection on rational points. -/
def torusLaurentEquiv : TorusRing K ≃ₐ[K] DoubleLaurent K where
  toFun := toLaurent K
  map_add' := (toLaurent K).map_add
  map_mul' := (toLaurent K).map_mul
  commutes' := (toLaurent K).commutes
  invFun := fromLaurent K
  left_inv a := DFunLike.congr_fun (fromLaurent_comp_toLaurent K) a
  right_inv := toLaurent_fromLaurent K

/-- In particular the defining ideal has no hidden nilpotent component. -/
instance torusRing_isDomain : IsDomain (TorusRing K) :=
  MulEquiv.isDomain (DoubleLaurent K) (torusLaurentEquiv K).toMulEquiv

instance torusRing_isReduced : _root_.IsReduced (TorusRing K) := inferInstance

theorem torusIdeal_isPrime : (torusIdeal K).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime (torusIdeal K)).mp (torusRing_isDomain K)

/-- The actual affine scheme is isomorphic to the Laurent torus. -/
def torusSchemeLaurentIso : torusScheme K ≅ Spec (.of (DoubleLaurent K)) :=
  Scheme.Spec.mapIso (torusLaurentEquiv K).symm.toRingEquiv.toCommRingCatIso.op

instance torusScheme_isIntegral : AlgebraicGeometry.IsIntegral (torusScheme K) := by
  change AlgebraicGeometry.IsIntegral (Spec (.of (TorusRing K)))
  infer_instance

instance torusScheme_isReduced : AlgebraicGeometry.IsReduced (torusScheme K) := inferInstance

/-- The fixed affine four-space embedding is induced by the original
quotient homomorphism. -/
def torusAffineEmbedding : torusScheme K ⟶ Spec (.of (MvPolynomial (Fin 4) K)) :=
  Spec.map (CommRingCat.ofHom (quotient K).toRingHom)

instance torusAffineEmbedding_isClosedImmersion : IsClosedImmersion (torusAffineEmbedding K) := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (torusIdeal K))))
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end PrimeGap182.TypeIII.PhysicalTorusLaurent

#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.variableUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.variableUnit_pow
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.DoubleLaurent
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.laurentX
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.laurentY
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.toLaurent
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.innerEvaluation
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.fromLaurent
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.fromLaurent_C
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.fromLaurent_T
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.innerEvaluation_C
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.innerEvaluation_T
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.evaluation_natural
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.evaluation_identity
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.map_fromLaurent_laurentX
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.map_fromLaurent_laurentY
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.fromLaurent_comp_toLaurent
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.map_toLaurent_xUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.map_toLaurent_yUnit
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.laurentX_pow
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.laurentY_pow
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.toLaurent_xUnit_pow
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.toLaurent_yUnit_pow
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.toLaurent_innerEvaluation
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.toLaurent_fromLaurent
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusLaurentEquiv
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusRing_isDomain
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusRing_isReduced
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusIdeal_isPrime
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusSchemeLaurentIso
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusScheme_isIntegral
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusScheme_isReduced
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusAffineEmbedding
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.torusAffineEmbedding_isClosedImmersion
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.toLaurent.eq_1
#print axioms PrimeGap182.TypeIII.PhysicalTorusLaurent.variableUnit.eq_1
