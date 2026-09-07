import TypeIIILocal
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FinCases

/-!
# Bounded fibers of the actual exceptional plane curve

This file proves the finite-fiber consequence of the nonzero bounded-degree polynomial in
`CurveExceptionalFourierBound`. It assumes no sheaf-theoretic or asymptotic result. The
coefficient field may be an algebraic closure; the points being counted lie in the actual
prime field through its injective algebra map.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

private theorem finite_roots_card_le
    {K F : Type*} [Field K] [Fintype F] (ι : F → K) (hι : Function.Injective ι)
    (P : Polynomial K) (hP : P ≠ 0) :
    (Finset.univ.filter (fun x : F => P.eval (ι x) = 0)).card ≤ P.natDegree := by
  classical
  let S := Finset.univ.filter (fun x : F => P.eval (ι x) = 0)
  change S.card ≤ P.natDegree
  by_contra! hcard
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (ι := {x // x ∈ S}) (f := fun x => ι x.val) (hι.comp Subtype.val_injective)
  · intro x
    exact (Finset.mem_filter.mp x.property).2
  · simpa using hcard

private theorem uniquePolynomial_natDegree_le
    {K : Type*} [Field K] (P : MvPolynomial (Fin 1) K) :
    (MvPolynomial.uniqueAlgEquiv K (Fin 1) P).natDegree ≤ P.totalDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  change P.totalDegree < (Finsupp.single (0 : Fin 1) n).sum (fun _ e => e)
  simpa using hn

private theorem plane_horizontal_fibers
    {K F : Type*} [Field K] [Fintype F] (ι : F → K) (hι : Function.Injective ι)
    (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0) :
    ∃ V : Finset F, V.card ≤ P.totalDegree ∧
      ∀ x : F, x ∉ V →
        (Finset.univ.filter (fun y : F => MvPolynomial.eval ![ι y, ι x] P = 0)).card ≤
          P.totalDegree := by
  classical
  let Q := MvPolynomial.finSuccEquiv K 1 P
  have hQ : Q ≠ 0 := by
    intro hz
    apply hP
    apply (MvPolynomial.finSuccEquiv K 1).injective
    simpa [Q] using hz
  let A := Q.leadingCoeff
  have hA : A ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  let b := MvPolynomial.uniqueAlgEquiv K (Fin 1) A
  have hb : b ≠ 0 := by
    intro hz
    apply hA
    apply (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective
    simpa [b] using hz
  have hdegA : A.totalDegree ≤ P.totalDegree := by
    have hh := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P Q.natDegree hA
    exact (Nat.le_add_right _ _).trans hh
  have hdegb : b.natDegree ≤ P.totalDegree :=
    (uniquePolynomial_natDegree_le A).trans hdegA
  have hdegQ : Q.natDegree ≤ P.totalDegree := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree P 0
  let V := Finset.univ.filter (fun x : F => b.eval (ι x) = 0)
  refine ⟨V, (finite_roots_card_le ι hι b hb).trans hdegb, ?_⟩
  intro x hx
  have hx' : b.eval (ι x) ≠ 0 := by simpa [V] using hx
  let Qx := Q.map (MvPolynomial.eval (fun _ : Fin 1 => ι x))
  have hb_eval : b.eval (ι x) = MvPolynomial.eval (fun _ : Fin 1 => ι x) A := by
    simpa [b] using
      (MvPolynomial.eval₂_const_uniqueAlgEquiv (f := A) (φ := RingHom.id K) (a := ι x))
  have hQx : Qx ≠ 0 := by
    intro hz
    apply hx'
    rw [hb_eval]
    have hh := congrArg (fun T : Polynomial K => T.coeff Q.natDegree) hz
    change MvPolynomial.eval (fun _ : Fin 1 => ι x) (Q.coeff Q.natDegree) = 0
    simpa only [Qx, Polynomial.coeff_map, Polynomial.coeff_zero] using hh
  have heval (y : F) : Qx.eval (ι y) = MvPolynomial.eval ![ι y, ι x] P := by
    have hvec : Fin.cons (ι y) (fun _ : Fin 1 => ι x) = ![ι y, ι x] := by
      funext i
      fin_cases i <;> rfl
    simpa only [Qx, Q, hvec] using
      (MvPolynomial.eval_eq_eval_mv_eval' (fun _ : Fin 1 => ι x) (ι y) P).symm
  have hroots := finite_roots_card_le ι hι Qx hQx
  simp_rw [heval] at hroots
  exact hroots.trans ((Polynomial.natDegree_map_le).trans hdegQ)

/-- A nonzero plane polynomial has at most its total degree many exceptional vertical
fibers; every other vertical fiber contains at most its total degree many points from any
fixed finite set embedded in the coefficient field. -/
theorem plane_vertical_fibers
    {K F : Type*} [Field K] [Fintype F] (ι : F → K) (hι : Function.Injective ι)
    (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0) :
    ∃ V : Finset F, V.card ≤ P.totalDegree ∧
      ∀ x : F, x ∉ V →
        (Finset.univ.filter (fun y : F => MvPolynomial.eval ![ι x, ι y] P = 0)).card ≤
          P.totalDegree := by
  classical
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let Q := MvPolynomial.renameEquiv K e P
  have hQ : Q ≠ 0 := by
    intro hz
    apply hP
    apply (MvPolynomial.renameEquiv K e).injective
    simpa [Q] using hz
  have hdeg : Q.totalDegree = P.totalDegree := MvPolynomial.totalDegree_renameEquiv e P
  have heval (x y : F) : MvPolynomial.eval ![ι y, ι x] Q =
      MvPolynomial.eval ![ι x, ι y] P := by
    simp only [Q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
    apply congrArg (fun f : Fin 2 → K => MvPolynomial.eval f P)
    funext i
    fin_cases i <;> simp [e]
  obtain ⟨V, hV, hfiber⟩ := plane_horizontal_fibers ι hι Q hQ
  refine ⟨V, hV.trans_eq hdeg, ?_⟩
  intro x hx
  simpa only [heval, hdeg] using hfiber x hx

variable (p : ℕ) [Fact p.Prime]

/-- The actual prime-field zero set of the geometric curve polynomial. -/
def curveZeroSet (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun z => planeEval p P z.1 z.2 = 0)

@[simp] theorem mem_curveZeroSet
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) (h k : ZMod p) :
    (h, k) ∈ curveZeroSet p P ↔ planeEval p P h k = 0 := by
  classical
  unfold curveZeroSet
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The combinatorial property required by the subsequent CRT/frequency averaging. -/
def BoundedVerticalFibers (s : ℕ) [NeZero s]
    (D : ℕ) (E : Finset (ZMod s × ZMod s)) : Prop :=
  ∃ V : Finset (ZMod s), V.card ≤ D ∧
    ∀ h : ZMod s, h ∉ V →
      (Finset.univ.filter (fun k : ZMod s => (h, k) ∈ E)).card ≤ D

/-- The bounded-fiber property is derived from the curve witness; it is not a new input. -/
theorem curveZeroSet_boundedVerticalFibers
    (D : ℕ) (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)))
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D) :
    BoundedVerticalFibers p D (curveZeroSet p P) := by
  classical
  obtain ⟨V, hV, hfiber⟩ := plane_vertical_fibers
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective P hP
  refine ⟨V, hV.trans hD, ?_⟩
  intro h hh
  have hcard : (Finset.univ.filter (fun k : ZMod p => (h, k) ∈ curveZeroSet p P)).card ≤
      P.totalDegree := by
    simp_rw [mem_curveZeroSet]
    exact hfiber h hh
  exact hcard.trans hD

/-- Extract the exact finite frequency set and its proved fiber bounds from the explicit
algebraic-curve Fourier hypothesis. -/
theorem CurveExceptionalFourierBound.finite_fibers
    {C : ℝ} {D : ℕ} {α m m' n n' : ZMod p}
    (hbound : CurveExceptionalFourierBound p C D α m m' n n') :
    ∃ E : Finset (ZMod p × ZMod p), BoundedVerticalFibers p D E ∧
      ∀ h k : ZMod p,
        ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
          C * (p : ℝ) ^ 3 *
            (1 + Real.sqrt (p : ℝ) * (if (h, k) ∈ E then 1 else 0) +
              (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0) := by
  classical
  obtain ⟨P, hP, hD, hF⟩ := hbound
  refine ⟨curveZeroSet p P, curveZeroSet_boundedVerticalFibers p D P hP hD, ?_⟩
  intro h k
  simpa [curveZeroSet] using hF h k

#print axioms plane_vertical_fibers
#print axioms curveZeroSet_boundedVerticalFibers
#print axioms CurveExceptionalFourierBound.finite_fibers

end

end PrimeGap182.TypeIII
