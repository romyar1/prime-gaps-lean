import TypeIIIPureDualTrace
import TypeIIIImageWeightsFromCompact
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Ordinary-dual point spectra from the same evaluation

The general lisse dual-stalk comparison is required to realize the original
evaluation morphism. It contains no Frobenius or spectral equation. Naturality
and the existing monoidal point-stalk laws force the contragredient operator.
Characteristic-polynomial inversion then retains every algebraic multiplicity.
No semisimplicity, purity, or existence of a complete input family is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite Polynomial
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation
open SourceInverseImageSystem RationalPointStalks

section Linear
universe u

private theorem reverse_linear (a : ℂ) (ha : a ≠ 0) :
    (X - C a).reverse = C (-a) * (X - C a⁻¹) := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by simpa only [C_1] using reverse_C (1 : ℂ)
  have hX : (X : ℂ[X]).reverse = 1 := by
    simpa only [one_mul, h1] using reverse_mul_X (1 : ℂ[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, mul_sub, ← C_mul]
  simp only [neg_mul, mul_inv_cancel₀ ha, C_neg, C_1]
  ring

private theorem reverse_product_roots (s : Multiset ℂ) (hs : ∀ a ∈ s, a ≠ 0) :
    ((s.map fun a => X - C a).prod.reverse).roots = s.map Inv.inv := by
  induction s using Multiset.induction_on with
  | empty => simp [show (1 : ℂ[X]).reverse = 1 by simpa using reverse_C (1 : ℂ)]
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hs' : ∀ b ∈ s, b ≠ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [reverse_mul_of_domain, reverse_linear a ha, mul_assoc, roots_C_mul _ (neg_ne_zero.mpr ha),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (by
        intro h
        exact (monic_multisetProd_X_sub_C s).ne_zero (reverse_eq_zero.mp h))),
      roots_X_sub_C, ih hs']
    rfl

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Transposing an endomorphism preserves its full characteristic polynomial. -/
theorem charpoly_dual (f : V →ₗ[ℂ] V) : f.dualMap.charpoly = f.charpoly := by
  let b := Module.Free.chooseBasis ℂ V
  rw [← LinearMap.charpoly_toMatrix f.dualMap b.dualBasis,
    ← LinearMap.charpoly_toMatrix f b]
  change (LinearMap.toMatrix b.dualBasis b.dualBasis
    (Module.Dual.transpose (R := ℂ) f)).charpoly = _
  rw [LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

/-- Inverse operators have reciprocal characteristic roots, with multiplicity. -/
theorem roots_inverse (f : V ≃ₗ[ℂ] V) :
    f.symm.toLinearMap.charpoly.roots = f.toLinearMap.charpoly.roots.map Inv.inv := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  let A := LinearMap.toMatrix b b f.toLinearMap
  let C' := LinearMap.toMatrix b b f.symm.toLinearMap
  have hAC : A * C' = 1 := by
    rw [← LinearMap.toMatrix_comp]
    simp [LinearEquiv.comp_coe]
  have hCA : C' * A = 1 := by
    rw [← LinearMap.toMatrix_comp]
    simp [LinearEquiv.comp_coe]
  have hA : IsUnit A := ⟨⟨A, C', hAC, hCA⟩, rfl⟩
  have hC' : C' = A⁻¹ := by
    exact (Matrix.inv_eq_left_inv hCA).symm
  have hd : A.det ≠ 0 := (isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det A).mp hA))
  have hs : ∀ a ∈ A.charpoly.roots, a ≠ 0 := by
    intro a ha
    rw [LinearMap.charpoly_toMatrix] at ha
    exact ImageWeightsFromCompact.root_ne_zero f.toLinearMap f.injective ha
  rw [← LinearMap.charpoly_toMatrix f.symm.toLinearMap b]
  change C'.charpoly.roots = _
  rw [hC', Matrix.charpoly_inv A hA, ← Matrix.reverse_charpoly]
  rw [Ring.inverse_eq_inv]
  rw [show (-1 : ℂ[X]) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ V) *
      C A.det⁻¹ = C ((-1 : ℂ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℂ V) * A.det⁻¹) by
      simp]
  rw [roots_C_mul _ (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by simpa using inv_ne_zero hd))]
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic A)]
  rw [reverse_product_roots _ hs, LinearMap.charpoly_toMatrix]

end Linear

universe mu
variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)}
  (R : RationalPointStalks.Data B) (T : PointTraceFromTensor.Laws R)
  (X : Space (ZMod p)) (dual : (B.Obj X)ᵒᵖ ⥤ B.Obj X)
  (ev : ∀ A, dual.obj (op A) ⊗ A ⟶ 𝟙_ (B.Obj X))

/-- The pairing is the image of the original evaluation, through the exact
monoidal tensor and unit comparisons of the original rational-point stalk. -/
def pairing (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X)
    (u : (R.fiber E X x).obj (dual.obj (op A))) (v : (R.fiber E X x).obj A) : ℂ := by
  letI := T.monoidal E X x
  exact (Functor.Monoidal.εIso (R.fiber E X x)).toLinearEquiv.symm
    (((R.fiber E X x).map (ev A)).hom
      ((Functor.Monoidal.μIso (R.fiber E X x) (dual.obj (op A)) A).toLinearEquiv
        (u ⊗ₜ[ℂ] v)))

variable (Lisse : B.Obj X → Prop)

/-- General ordinary-dual stalk realization, guarded only by original lissity.
The comparison realizes the same evaluation and supplies no arithmetic law. -/
structure Comparison where
  equiv : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] x A,
    Lisse A → (R.fiber E X x).obj (dual.obj (op A)) ≃ₗ[ℂ]
      Module.Dual ℂ ((R.fiber E X x).obj A)
  evaluation : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] x A
    (hA : Lisse A) u v, equiv E x A hA u v = pairing R T X dual ev E x A u v

variable {R T X dual ev Lisse}

/-- Naturality of the same evaluation plus tensor and unit Frobenius laws
forces invariance of its stalk pairing. -/
theorem pairing_invariant (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X)
    (u : (R.fiber E X x).obj (dual.obj (op A))) (v : (R.fiber E X x).obj A) :
    pairing R T X dual ev E x A
      (((R.frobenius E X x).app (dual.obj (op A))).hom u)
      (((R.frobenius E X x).app A).hom v) = pairing R T X dual ev E x A u v := by
  let := T.monoidal E X x
  unfold pairing
  rw [← TensorProduct.map_tmul, T.tensor E X x]
  have hn := congrArg (fun m => m.hom
    ((Functor.Monoidal.μIso (R.fiber E X x) (dual.obj (op A)) A).toLinearEquiv
      (u ⊗ₜ[ℂ] v))) ((R.frobenius E X x).naturality (ev A))
  change ((R.frobenius E X x).app (𝟙_ (B.Obj X))).hom
      (((R.fiber E X x).map (ev A)).hom _) =
    ((R.fiber E X x).map (ev A)).hom
      (((R.frobenius E X x).app (dual.obj (op A) ⊗ A)).hom _) at hn
  rw [← hn]
  let e := (Functor.Monoidal.εIso (R.fiber E X x)).toLinearEquiv
  obtain ⟨z, hz⟩ := e.surjective
    (((R.fiber E X x).map (ev A)).hom
      ((Functor.Monoidal.μIso (R.fiber E X x) (dual.obj (op A)) A).toLinearEquiv (u ⊗ₜ[ℂ] v)))
  rw [← hz, T.unit E X x]

/-- Read the original Frobenius as an equivalence using its existing IsIso law. -/
def frobeniusEquiv (I : ImageWeightsFromCompact.Automorphisms R)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X) :
    (R.fiber E X x).obj A ≃ₗ[ℂ] (R.fiber E X x).obj A := by
  letI := I.isIso E X x A
  exact (asIso ((R.frobenius E X x).app A)).toLinearEquiv

/-- The dual operator is conjugate to the transpose of the inverse of the
original Frobenius; this is derived, rather than a comparison premise. -/
theorem contragredient (P : Comparison R T X dual ev Lisse)
    (I : ImageWeightsFromCompact.Automorphisms R)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X) (hA : Lisse A) :
    (P.equiv E x A hA).conj (((R.frobenius E X x).app (dual.obj (op A))).hom) =
      (frobeniusEquiv I E x A).symm.toLinearMap.dualMap := by
  ext u v
  let f := frobeniusEquiv I E x A
  change P.equiv E x A hA
      (((R.frobenius E X x).app (dual.obj (op A))).hom ((P.equiv E x A hA).symm u)) v =
    u (f.symm v)
  rw [P.evaluation E x A hA]
  have hi := pairing_invariant (R := R) (T := T) (dual := dual) (ev := ev)
    E x A ((P.equiv E x A hA).symm u) (f.symm v)
  change pairing R T X dual ev E x A
      (((R.frobenius E X x).app (dual.obj (op A))).hom ((P.equiv E x A hA).symm u))
      (f (f.symm v)) = _ at hi
  rw [f.apply_symm_apply] at hi
  rw [hi, ← P.evaluation E x A hA, LinearEquiv.apply_symm_apply]

/-- The old twist-zero spectral interface follows with all characteristic
multiplicities from the same lisse evaluation and original stalk operators. -/
theorem dualSpectrum (P : Comparison R T X dual ev Lisse)
    (I : ImageWeightsFromCompact.Automorphisms R) :
    PureDualTrace.DualSpectrum R X dual Lisse 0 where
  roots E _ _ _ x A hA := by
    let := R.finite E X x A
    let := R.finite E X x (dual.obj (op A))
    let f := frobeniusEquiv I E x A
    have hc := contragredient P I E x A hA
    change (P.equiv E x A hA).conj
      (((R.frobenius E X x).app (dual.obj (op A))).hom) = f.symm.toLinearMap.dualMap at hc
    unfold PureDualTrace.eigenvalues
    rw [← LinearEquiv.charpoly_conj (P.equiv E x A hA), hc, charpoly_dual, roots_inverse f]
    simp only [pow_zero, one_div]
    rfl

end PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation

#print axioms PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation.charpoly_dual
#print axioms PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation.roots_inverse
#print axioms PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation.pairing_invariant
#print axioms PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation.contragredient
#print axioms PrimeGap182.TypeIII.PointDualSpectrumFromEvaluation.dualSpectrum
