import TypeIIIPublishedStalkSupport

/-!
# Common Type III stalk certificates from explicit published-rule hypotheses

`TraceWeightRules` records the generic trace and weight conventions for
chosen Weil lifts: a pure perverse object is geometrically semisimple, its ordinary stalk degrees have
the corresponding Deligne weight bounds, and the plane Fourier--Deligne
transform with shift `[2]` and no Tate normalization raises weight by two.
The trace formula has the positive, unnormalized `fourier₂` convention.
These are explicit hypotheses, not a realization of the foundational adic
construction. See the primary references in
`research/type_iii/published_inputs/support_and_weights_audit.md`.

`FamilyConstruction` is separate application data. It contains the physical
objects and their Weil lifts, their actual corrected-factor trace on the unit torus, purity of
weight `|S|+2`, full support of physical constituents, and explicit numerical
bounds on the QST functions at the physical and transformed objects. None of
these family assertions is presented as a general published theorem.

The resulting common certificate uses the actual unit torus as its physical
open set, with boundary cardinality at most `2*p`, hence `Dphys = 1`. Physical
exceptional sets and degree-zero vanishing are derived from the BBD/QST
rules. The transformed data are literally the rational realization of the
Fourier objects. No transformed support restriction or Fourier norm bound
is an input or conclusion of this file. Uniform dimension/support constants
are supplied explicitly; no monotonicity of the QST functions is assumed.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.PublishedStalkCertificate

open PublishedSupportRules PublishedStalkSupport

universe u

/-- The actual rational points of the unit torus in the physical plane. -/
def torusOpen (p : ℕ) [Fact p.Prime] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun z => z.1 ≠ 0 ∧ z.2 ≠ 0

@[simp] theorem mem_torusOpen (p : ℕ) [Fact p.Prime] (z : ZMod p × ZMod p) :
    z ∈ torusOpen p ↔ z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  simp [torusOpen]

/-- The physical boundary is contained in the two coordinate axes, whose
cardinalities sum to `2*p`. Their common origin causes no difficulty. -/
theorem torusOpen_complement_card_le (p : ℕ) [Fact p.Prime] :
    (Finset.univ \ torusOpen p).card ≤ 2 * p := by
  have hsubset : Finset.univ \ torusOpen p ⊆
      (Finset.univ ×ˢ ({0} : Finset (ZMod p))) ∪
        (({0} : Finset (ZMod p)) ×ˢ Finset.univ) := by
    intro z hz
    have hnot := (Finset.mem_sdiff.mp hz).2
    by_cases hx : z.1 = 0
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hx, Finset.mem_univ _⟩)
    · have hy : z.2 = 0 := by
        by_contra hy
        exact hnot ((mem_torusOpen p z).mpr ⟨hx, hy⟩)
      exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_singleton.mpr hy⟩)
  calc
    _ ≤ ((Finset.univ ×ˢ ({0} : Finset (ZMod p))) ∪
        (({0} : Finset (ZMod p)) ×ˢ Finset.univ)).card := Finset.card_le_card hsubset
    _ ≤ (Finset.univ ×ˢ ({0} : Finset (ZMod p))).card +
        (({0} : Finset (ZMod p)) ×ˢ Finset.univ).card := Finset.card_union_le _ _
    _ = 2 * p := by simp [two_mul]

/-- Generic published trace and weight rules for the chosen rational
realization and Fourier operation. No Type III family occurs in a field. -/
structure TraceWeightRules (p : ℕ) [Fact p.Prime] {Obj : Type u}
    (D : SurfaceData (AlgebraicClosure (ZMod p)) Obj)
    (realization : RationalStalkRealization p D) (fourier : Obj → Obj) where
  PureOfWeight : {P : Obj} → realization.WeilLift P → ℝ → Prop
  pure : ∀ {P} (W : realization.WeilLift P) w, PureOfWeight W w → D.Pure P
  rational_weights : ∀ {P} (W : realization.WeilLift P) w, PureOfWeight W w → ∀ x y,
    (realization.stalk W x y).weightsLe p w
  fourierLift : {P : Obj} → realization.WeilLift P → realization.WeilLift (fourier P)
  fourier_purity : ∀ {P} (W : realization.WeilLift P) w,
    PureOfWeight W w → PureOfWeight (fourierLift W) (w + 2)
  fourier_trace : ∀ {P} (W : realization.WeilLift P) h k,
    (realization.stalk (fourierLift W) h k).trace =
      fourier₂ p (fun x y => (realization.stalk W x y).trace) h k

/-- Dimension control is derived from the geometric QST bound and the
proved meaning of the rational realization's three degree dimensions. -/
theorem rational_dimensionsLe_of_qst {p : ℕ} [Fact p.Prime] {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    (qst : QSTRules D) (realization : RationalStalkRealization p D)
    (Q : Obj) (W : realization.WeilLift Q)
    (B : ℕ) (hbound : qst.stalkBound (D.complexity Q) ≤ B)
    (x y : ZMod p) : (realization.stalk W x y).dimensionsLe B := by
  refine ⟨?_, ?_, ?_⟩
  · rw [realization.minusTwo_dimension W x y]
    exact (qst.geomDim_le Q (primeFieldPoint p (x, y)) 0).trans hbound
  · rw [realization.minusOne_dimension W x y]
    exact (qst.geomDim_le Q (primeFieldPoint p (x, y)) 1).trans hbound
  · rw [realization.zero_dimension W x y]
    exact (qst.geomDim_le Q (primeFieldPoint p (x, y)) 2).trans hbound

/-- Actual-family construction/application inputs, distinct from the
generic imported laws. `B` and `Rphys` are the supplied uniform constants;
their bounds are evaluated directly at each actual object's complexity. -/
structure FamilyConstruction (B Rphys : ℕ) (p : ℕ) [Fact p.Prime]
    (α m m' n n' : ZMod p) {Obj : Type u}
    (D : SurfaceData (AlgebraicClosure (ZMod p)) Obj) (qst : QSTRules D)
    (realization : RationalStalkRealization p D) (fourier : Obj → Obj)
    (rules : TraceWeightRules p D realization fourier) where
  physicalObjects : Finset (Fin 4) → Obj
  physicalLift : ∀ S, realization.WeilLift (physicalObjects S)
  trace_on_units : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, x ≠ 0 → y ≠ 0 →
    (realization.stalk (physicalLift S) x y).trace =
      ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y
  pure_weight : ∀ S ∈ nonemptyCoreSubsets,
    rules.PureOfWeight (physicalLift S) ((S.card : ℝ) + 2)
  full_constituents : ∀ S ∈ nonemptyCoreSubsets,
    D.NoProperConstituents (physicalObjects S)
  physical_stalk_bound : ∀ S ∈ nonemptyCoreSubsets,
    qst.stalkBound (D.complexity (physicalObjects S)) ≤ B
  transformed_stalk_bound : ∀ S ∈ nonemptyCoreSubsets,
    qst.stalkBound (D.complexity (fourier (physicalObjects S))) ≤ B
  physical_support_bound : ∀ S ∈ nonemptyCoreSubsets,
    qst.ordinarySupportBound (D.complexity (physicalObjects S)) ≤ Rphys

namespace FamilyConstruction

variable {B Rphys p : ℕ} [Fact p.Prime] {α m m' n n' : ZMod p} {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj} {qst : QSTRules D}
    {realization : RationalStalkRealization p D} {fourier : Obj → Obj}
    {rules : TraceWeightRules p D realization fourier}
    (family : FamilyConstruction B Rphys p α m m' n n' D qst realization fourier rules)

theorem physical_pure (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) :
    D.Pure (family.physicalObjects S) :=
  rules.pure _ _ (family.pure_weight S hS)

/-- The `+4` weight is derived from physical weight `|S|+2` and the generic
unnormalized two-dimensional Fourier purity rule. -/
theorem transformed_pure_weight (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) :
    rules.PureOfWeight (rules.fourierLift (family.physicalLift S))
      ((S.card : ℝ) + 4) := by
  simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using
    rules.fourier_purity _ _ (family.pure_weight S hS)

theorem transformed_pure (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) :
    D.Pure (fourier (family.physicalObjects S)) :=
  rules.pure _ _ (family.transformed_pure_weight S hS)

/-- The original common Type III certificate, with literal spectra and
unit-torus physical open set. The exceptional sets are constructed from
the generic geometric support theorems, not supplied in the family data. -/
def certificate (bbd : BBDRules D) :
    TypeIIIStalkCertificate p B 1 Rphys α m m' n n' := by
  have hexists : ∀ S : Finset (Fin 4), ∃ Z : Finset (ZMod p × ZMod p),
      ∀ hS : S ∈ nonemptyCoreSubsets,
        Z.card ≤ Rphys ∧
        (∀ x y, (x, y) ∉ Z →
          (realization.stalk (family.physicalLift S) x y).minusOne.dimension = 0) ∧
        (∀ x y, (realization.stalk (family.physicalLift S) x y).zero.dimension = 0) := by
    intro S
    by_cases hS : S ∈ nonemptyCoreSubsets
    · obtain ⟨Z, hcard, hminus, hzero⟩ := exists_finite_rational_support bbd qst
        realization (family.physicalObjects S) (family.physicalLift S) (family.physical_pure S hS)
        (family.full_constituents S hS)
      exact ⟨Z, fun _ => ⟨hcard.trans (family.physical_support_bound S hS), hminus, hzero⟩⟩
    · exact ⟨∅, fun h => (hS h).elim⟩
  choose exceptional hexceptional using hexists
  refine {
    physicalOpen := torusOpen p
    physical := fun S => realization.stalk (family.physicalLift S)
    transformed := fun S => realization.stalk (rules.fourierLift (family.physicalLift S))
    physicalExceptional := exceptional
    complement_card := ?_
    physicalExceptional_card := fun S hS => (hexceptional S hS).1
    trace_on := ?_
    fourier_trace := fun S _ h k => rules.fourier_trace (family.physicalLift S) h k
    physical_dimensions := fun S hS x y => rational_dimensionsLe_of_qst qst
      realization (family.physicalObjects S) (family.physicalLift S) B
      (family.physical_stalk_bound S hS) x y
    physical_weights := fun S hS x y => rules.rational_weights _ _
      (family.pure_weight S hS) x y
    physical_minusOne := fun S hS x y hnot => (hexceptional S hS).2.1 x y hnot
    physical_zero := fun S hS x y => (hexceptional S hS).2.2 x y
    transformed_dimensions := fun S hS h k => rational_dimensionsLe_of_qst qst
      realization (fourier (family.physicalObjects S))
      (rules.fourierLift (family.physicalLift S)) B
      (family.transformed_stalk_bound S hS) h k
    transformed_weights := fun S hS h k => rules.rational_weights _ _
      (family.transformed_pure_weight S hS) h k }
  · simpa only [Nat.mul_one] using torusOpen_complement_card_le p
  · intro S hS x y hxy
    exact family.trace_on_units S hS x y ((mem_torusOpen p (x, y)).mp hxy).1
      ((mem_torusOpen p (x, y)).mp hxy).2

@[simp] theorem certificate_physicalOpen (bbd : BBDRules D) :
    (family.certificate bbd).physicalOpen = torusOpen p := rfl

@[simp] theorem certificate_physical (bbd : BBDRules D) (S : Finset (Fin 4))
    (x y : ZMod p) :
    (family.certificate bbd).physical S x y =
      realization.stalk (family.physicalLift S) x y := rfl

@[simp] theorem certificate_transformed (bbd : BBDRules D) (S : Finset (Fin 4))
    (h k : ZMod p) :
    (family.certificate bbd).transformed S h k =
      realization.stalk (rules.fourierLift (family.physicalLift S)) h k := rfl

end FamilyConstruction

#print axioms torusOpen
#print axioms mem_torusOpen
#print axioms torusOpen_complement_card_le
#print axioms TraceWeightRules
#print axioms TraceWeightRules.mk
#print axioms TraceWeightRules.rec
#print axioms TraceWeightRules.recOn
#print axioms TraceWeightRules.casesOn
#print axioms TraceWeightRules.noConfusionType
#print axioms TraceWeightRules.noConfusion
#print axioms TraceWeightRules.PureOfWeight
#print axioms TraceWeightRules.pure
#print axioms TraceWeightRules.rational_weights
#print axioms TraceWeightRules.fourierLift
#print axioms TraceWeightRules.fourier_purity
#print axioms TraceWeightRules.fourier_trace
#print axioms rational_dimensionsLe_of_qst
#print axioms FamilyConstruction
#print axioms FamilyConstruction.mk
#print axioms FamilyConstruction.rec
#print axioms FamilyConstruction.recOn
#print axioms FamilyConstruction.casesOn
#print axioms FamilyConstruction.noConfusionType
#print axioms FamilyConstruction.noConfusion
#print axioms FamilyConstruction.physicalObjects
#print axioms FamilyConstruction.physicalLift
#print axioms FamilyConstruction.trace_on_units
#print axioms FamilyConstruction.pure_weight
#print axioms FamilyConstruction.full_constituents
#print axioms FamilyConstruction.physical_stalk_bound
#print axioms FamilyConstruction.transformed_stalk_bound
#print axioms FamilyConstruction.physical_support_bound
#print axioms FamilyConstruction.physical_pure
#print axioms FamilyConstruction.transformed_pure_weight
#print axioms FamilyConstruction.transformed_pure
#print axioms FamilyConstruction.certificate
#print axioms FamilyConstruction.certificate_physicalOpen
#print axioms FamilyConstruction.certificate_physical
#print axioms FamilyConstruction.certificate_transformed

end PrimeGap182.TypeIII.PublishedStalkCertificate
