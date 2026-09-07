import TypeIIIPublishedApplicationBridge

/-!
# Uniform constants from one physical complexity bound

The quantitative-sheaf functions in this file are chosen before the prime.
The generic rules reconstruct the QST fields of `Theory` using those same
functions. No bound on an arbitrary prime-dependent choice of functions is
assumed. A finite maximum handles the possibly nonmonotone function in
QST Proposition 6.24; Fourier complexity uses the uniform multiplier in
Proposition 7.18 (the affine dimension is fixed at two).

Given a physical family of complexity at most `M`, the seven numerical
application bounds are deductions. The existence of that single physical
complexity bound still has to follow from the construction and six-operation
bounds; it is not inferred from rank alone.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.PublishedUniformComplexity

open PublishedSupportRules PublishedStalkCertificate PublishedTypeIII
open PublishedApplicationBridge

universe u v

/-- A monotone upper envelope, without a monotonicity premise on `f`. -/
def envelope (f : ℕ → ℕ) (M : ℕ) : ℕ := (Finset.range (M + 1)).sup f

theorem le_envelope (f : ℕ → ℕ) {c M : ℕ} (hc : c ≤ M) : f c ≤ envelope f M :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hc))

theorem envelope_mono (f : ℕ → ℕ) {M N : ℕ} (h : M ≤ N) :
    envelope f M ≤ envelope f N :=
  Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right h 1))

/-- These functions and the Fourier multiplier are common to all primes,
coefficient fields and parameter choices at the fixed embedding dimensions. -/
structure Bounds where
  stalk : ℕ → ℕ
  ordinary : ℕ → ℕ
  degree : ℕ → ℕ
  proper : ℕ → ℕ
  constituent : ℕ → ℕ
  fourierMultiplier : ℕ
  fourierMultiplier_pos : 0 < fourierMultiplier

namespace Bounds

def transformedCap (b : Bounds) (M : ℕ) : ℕ := b.fourierMultiplier * M
def stalkCap (b : Bounds) (M : ℕ) : ℕ := envelope b.stalk (max M (b.transformedCap M))
def physicalSupportCap (b : Bounds) (M : ℕ) : ℕ := envelope b.ordinary M
def exceptionalCap (b : Bounds) (M : ℕ) : ℕ :=
  max (envelope b.ordinary (b.transformedCap M)) (envelope b.degree (b.transformedCap M))
def properCap (b : Bounds) (M : ℕ) : ℕ := envelope b.proper (b.transformedCap M)
def punctualCap (b : Bounds) (M : ℕ) : ℕ := envelope b.constituent (b.transformedCap M)
def primeCutoff (b : Bounds) (M : ℕ) : ℕ := cutoff (b.properCap M) (b.punctualCap M)

end Bounds

variable {p : ℕ} [Fact p.Prime] (b : Bounds) (T : Theory.{u, v} p)

/-- Uniform published QST statements at fixed ambient dimension, expressed
using the shared functions. They concern every geometric object, independently
of the correlation family. Sources: QST Theorems 6.15, 6.23, Propositions 6.24,
7.1 and 7.18, and point pullback in Theorem 6.8. -/
structure Rules : Prop where
  geomDim_le : ∀ Q z i, T.data.geomDim Q z i ≤ b.stalk (T.data.complexity Q)
  ordinarySupport_ncard_le : ∀ Q i, (T.data.ordinarySupport Q i).Finite →
    (T.data.ordinarySupport Q i).ncard ≤ b.ordinary (T.data.complexity Q)
  constituent_length_le : ∀ Q,
    (T.data.constituents Q).length ≤ b.constituent (T.data.complexity Q)
  properSupport_polynomial : ∀ Q, ∃ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)),
    F ≠ 0 ∧ F.totalDegree ≤ b.proper (T.data.complexity Q) ∧
      ∀ z ∈ T.data.properSupportUnion Q, MvPolynomial.eval ![z.1, z.2] F = 0
  minusOne_polynomial : ∀ Q, ∃ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)),
    F ≠ 0 ∧ F.totalDegree ≤ b.degree (T.data.complexity Q) ∧
      ∀ z ∈ T.data.ordinarySupport Q 1, MvPolynomial.eval ![z.1, z.2] F = 0
  fourier_complexity : ∀ Q,
    T.data.complexity (T.fourier.fourier Q) ≤ b.fourierMultiplier * T.data.complexity Q

namespace Rules

variable {b T} (R : Rules b T)

/-- Reconstruct the bounds with the globally chosen functions. -/
def qst : QSTRules T.data where
  stalkBound := b.stalk
  ordinarySupportBound := b.ordinary
  constituentBound := b.constituent
  properDegreeBound := b.proper
  geomDim_le := R.geomDim_le
  ordinarySupport_ncard_le := R.ordinarySupport_ncard_le
  constituent_length_le := R.constituent_length_le
  properSupport_polynomial := R.properSupport_polynomial

def degrees : OrdinarySupportDegreeRules T.data where
  degreeBound := b.degree
  minusOne_polynomial := R.minusOne_polynomial

/-- All qualitative data, Weil lifts and operations are unchanged. Only
the quantitative witnesses are chosen uniformly instead of prime by prime. -/
def theory : Theory.{u, v} p := { T with qst := R.qst, degrees := R.degrees }

include R in
theorem transformed_complexity_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    T.data.complexity (T.fourier.fourier P) ≤ b.transformedCap M :=
  (R.fourier_complexity P).trans (Nat.mul_le_mul_left b.fourierMultiplier hP)

theorem physical_stalk_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.qst.stalkBound (T.data.complexity P) ≤ b.stalkCap M :=
  le_envelope b.stalk (hP.trans (le_max_left _ _))

theorem transformed_stalk_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.qst.stalkBound (T.data.complexity (T.fourier.fourier P)) ≤ b.stalkCap M :=
  le_envelope b.stalk ((R.transformed_complexity_le M P hP).trans (le_max_right _ _))

theorem physical_support_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.qst.ordinarySupportBound (T.data.complexity P) ≤ b.physicalSupportCap M :=
  le_envelope b.ordinary hP

theorem transformed_ordinary_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.qst.ordinarySupportBound (T.data.complexity (T.fourier.fourier P)) ≤
      b.exceptionalCap M :=
  (le_envelope b.ordinary (R.transformed_complexity_le M P hP)).trans (le_max_left _ _)

theorem transformed_degree_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.degrees.degreeBound (T.data.complexity (T.fourier.fourier P)) ≤
      b.exceptionalCap M :=
  (le_envelope b.degree (R.transformed_complexity_le M P hP)).trans (le_max_right _ _)

theorem transformed_proper_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.qst.properDegreeBound (T.data.complexity (T.fourier.fourier P)) ≤ b.properCap M :=
  le_envelope b.proper (R.transformed_complexity_le M P hP)

theorem transformed_punctual_le (M : ℕ) (P : T.Obj)
    (hP : T.data.complexity P ≤ M) :
    R.qst.constituentBound (T.data.complexity (T.fourier.fourier P)) ≤ b.punctualCap M :=
  le_envelope b.constituent (R.transformed_complexity_le M P hP)

/-- Construction of all physical numerical fields from one complexity
bound. The trace, purity and full-support data are still supplied by the
physical construction; this theorem proves none of them by assumption renaming. -/
def familyOfComplexity (M : ℕ) (α m m' n n' : ZMod p)
    (P : Finset (Fin 4) → T.Obj) (W : ∀ S, T.realization.WeilLift (P S))
    (htrace : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, x ≠ 0 → y ≠ 0 →
      (T.realization.stalk (W S) x y).trace =
        ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y)
    (hpure : ∀ S ∈ nonemptyCoreSubsets,
      T.traceWeights.PureOfWeight (W S) ((S.card : ℝ) + 2))
    (hfull : ∀ S ∈ nonemptyCoreSubsets, T.data.NoProperConstituents (P S))
    (hcomplexity : ∀ S ∈ nonemptyCoreSubsets, T.data.complexity (P S) ≤ M) :
    FamilyConstruction (b.stalkCap M) (b.physicalSupportCap M) p α m m' n n'
      R.theory.data R.theory.qst R.theory.realization
      R.theory.fourier.fourier R.theory.traceWeights where
  physicalObjects := P
  physicalLift := W
  trace_on_units := htrace
  pure_weight := hpure
  full_constituents := hfull
  physical_stalk_bound := fun S hS => R.physical_stalk_le M (P S) (hcomplexity S hS)
  transformed_stalk_bound := fun S hS => R.transformed_stalk_le M (P S) (hcomplexity S hS)
  physical_support_bound := fun S hS => R.physical_support_le M (P S) (hcomplexity S hS)

/-- The four transformed numerical fields use the same physical bound;
there is no additional family-specific exceptional-set bound. -/
theorem transformedBoundsOfComplexity (M B Rphys : ℕ) (α m m' n n' : ZMod p)
    (family : FamilyConstruction B Rphys p α m m' n n' R.theory.data R.theory.qst
      R.theory.realization R.theory.fourier.fourier R.theory.traceWeights)
    (hcomplexity : ∀ S ∈ nonemptyCoreSubsets,
      T.data.complexity (family.physicalObjects S) ≤ M) :
    TransformedBounds (theory := R.theory) (b.exceptionalCap M) (b.properCap M)
      (b.punctualCap M) family := {
  finite := fun S hS => R.transformed_ordinary_le M _ (hcomplexity S hS)
  curve := fun S hS => R.transformed_degree_le M _ (hcomplexity S hS)
  proper := fun S hS => R.transformed_proper_le M _ (hcomplexity S hS)
  punctual := fun S hS => R.transformed_punctual_le M _ (hcomplexity S hS) }

end Rules
end PrimeGap182.TypeIII.PublishedUniformComplexity

#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.envelope
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.le_envelope
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.envelope_mono
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.mk
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.stalk
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.ordinary
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.degree
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.proper
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.constituent
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.fourierMultiplier
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.fourierMultiplier_pos
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.transformedCap
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.stalkCap
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.physicalSupportCap
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.exceptionalCap
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.properCap
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.punctualCap
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Bounds.primeCutoff
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.mk
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.geomDim_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.ordinarySupport_ncard_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.constituent_length_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.properSupport_polynomial
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.minusOne_polynomial
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.fourier_complexity
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.qst
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.degrees
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.theory
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformed_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.physical_stalk_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformed_stalk_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.physical_support_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformed_ordinary_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformed_degree_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformed_proper_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformed_punctual_le
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.familyOfComplexity
#print axioms PrimeGap182.TypeIII.PublishedUniformComplexity.Rules.transformedBoundsOfComplexity
