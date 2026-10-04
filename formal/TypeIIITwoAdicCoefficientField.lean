import TypeIIIFinitePlaceScalarExtension
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.Complex

/-!
# The actual two-adic base of the coefficient field

The completed cyclotomic field is a finite extension of Q₂. Its fixed
algebraic closure is therefore an algebraic closure of Q₂ as well.
The scalar map is constructed from the original rational embedding.
-/

noncomputable section
open scoped Topology PrimeGap182.TypeIII.FinitePlaceScalarExtension

namespace PrimeGap182.TypeIII.TwoAdicCoefficientField

open NumberField IsDedekindDomain LocalCyclotomicCoefficient FinitePlaceScalarExtension

instance prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

def rationalPlace : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, by decide⟩

instance rationalPlace_over_two : rationalPlace.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) := by
  constructor
  ext x
  change x ∈ Ideal.span {(2 : ℤ)} ↔
    algebraMap ℤ (𝓞 ℚ) x ∈ (Ideal.span {(2 : ℤ)}).map
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom
  have he : (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm x = algebraMap ℤ (𝓞 ℚ) x := by
    exact congrArg (fun f : ℤ →+* 𝓞 ℚ => f x)
      (Subsingleton.elim (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom
        (algebraMap ℤ (𝓞 ℚ)))
  rw [← he]
  exact (Ideal.apply_mem_of_equiv_iff (I := Ideal.span {(2 : ℤ)})
    (f := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm) (x := x)).symm

def padicCongr (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (h : p = q) :
    ℚ_[p] ≃A[ℚ] ℚ_[q] := by
  subst q
  exact ContinuousAlgEquiv.refl ℚ ℚ_[p]

def rationalCompletionEquiv : rationalPlace.adicCompletion ℚ ≃A[ℚ] ℚ_[2] := by
  have hn : (Rat.HeightOneSpectrum.primesEquiv rationalPlace).val = 2 :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply
      ⟨2, by decide⟩)
  let : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv rationalPlace).val) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv rationalPlace).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv rationalPlace).trans
    (padicCongr _ 2 hn)

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [v.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})]

scoped instance liesOverRationalPlace : v.asIdeal.LiesOver rationalPlace.asIdeal := by
  constructor
  ext x
  obtain ⟨n, rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) x
  change algebraMap ℤ (𝓞 ℚ) n ∈ rationalPlace.asIdeal ↔
    algebraMap (𝓞 ℚ) (𝓞 K) (algebraMap ℤ (𝓞 ℚ) n) ∈ v.asIdeal
  rw [← Ideal.mem_of_liesOver rationalPlace.asIdeal (Ideal.span {(2 : ℤ)}),
    ← IsScalarTower.algebraMap_apply,
    ← Ideal.mem_of_liesOver v.asIdeal (Ideal.span {(2 : ℤ)})]

def padicEmbedding : ℚ_[2] →+* LocalField K v :=
  (completionMap ℚ K rationalPlace v).comp rationalCompletionEquiv.symm.toRingHom

theorem padicEmbedding_continuous : Continuous (padicEmbedding K v) :=
  (completionMap_continuous ℚ K rationalPlace v).comp rationalCompletionEquiv.symm.continuous

theorem padicEmbedding_rat (x : ℚ) :
    padicEmbedding K v (x : ℚ_[2]) = embedding K v (algebraMap ℚ K x) := by
  change completionMap ℚ K rationalPlace v
    (rationalCompletionEquiv.symm (algebraMap ℚ ℚ_[2] x)) = _
  have h : rationalCompletionEquiv.symm (algebraMap ℚ ℚ_[2] x) =
      algebraMap ℚ (rationalPlace.adicCompletion ℚ) x :=
    rationalCompletionEquiv.symm.commutes x
  rw [h]
  exact completionMap_on_base ℚ K rationalPlace v x

scoped instance localAlgebra : Algebra ℚ_[2] (LocalField K v) :=
  (padicEmbedding K v).toAlgebra

scoped instance localContinuousSMul : ContinuousSMul ℚ_[2] (LocalField K v) where
  continuous_smul := (padicEmbedding_continuous K v).comp continuous_fst |>.mul continuous_snd

theorem localFiniteDimensional : FiniteDimensional ℚ_[2] (LocalField K v) := by
  let : FiniteDimensional (rationalPlace.adicCompletion ℚ) (LocalField K v) :=
    finiteDimensional ℚ K rationalPlace v
  have h := Algebra.finrank_eq_of_equiv_equiv rationalCompletionEquiv.symm.toRingEquiv
    (RingEquiv.refl (LocalField K v)) (show
      (algebraMap (rationalPlace.adicCompletion ℚ) (LocalField K v)).comp
        rationalCompletionEquiv.symm.toRingHom =
          (RingEquiv.refl (LocalField K v)).toRingHom.comp
            (algebraMap ℚ_[2] (LocalField K v)) from rfl)
  apply Module.finite_of_finrank_pos
  rw [h]
  exact Module.finrank_pos

scoped instance coeffAlgebra : Algebra ℚ_[2] (ClosedCyclotomicCoefficient.Coeff K v) :=
  ((algebraMap (LocalField K v) (ClosedCyclotomicCoefficient.Coeff K v)).comp
    (algebraMap ℚ_[2] (LocalField K v))).toAlgebra

scoped instance coeffScalarTower :
    IsScalarTower ℚ_[2] (LocalField K v) (ClosedCyclotomicCoefficient.Coeff K v) :=
  .of_algebraMap_eq (fun _ => rfl)

scoped instance coeffIsAlgClosure :
    IsAlgClosure ℚ_[2] (ClosedCyclotomicCoefficient.Coeff K v) where
  isAlgClosed := inferInstance
  isAlgebraic := by
    let : FiniteDimensional ℚ_[2] (LocalField K v) := localFiniteDimensional K v
    exact Algebra.IsAlgebraic.trans ℚ_[2] (LocalField K v) (ClosedCyclotomicCoefficient.Coeff K v)

/-- The same coefficient field, identified algebraically over Q₂ with
the standard algebraic closure. Topological compatibility is not asserted here. -/
def coefficientEquiv : ClosedCyclotomicCoefficient.Coeff K v ≃ₐ[ℚ_[2]] PadicAlgCl 2 :=
  IsAlgClosure.equiv ℚ_[2] _ _

end PrimeGap182.TypeIII.TwoAdicCoefficientField

#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.rationalPlace
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.rationalPlace_over_two
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.padicCongr
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.rationalCompletionEquiv
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.liesOverRationalPlace
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.padicEmbedding
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.padicEmbedding_continuous
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.padicEmbedding_rat
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.localAlgebra
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.localContinuousSMul
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.localFiniteDimensional
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.coeffAlgebra
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.coeffScalarTower
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.coeffIsAlgClosure
#print axioms PrimeGap182.TypeIII.TwoAdicCoefficientField.coefficientEquiv
