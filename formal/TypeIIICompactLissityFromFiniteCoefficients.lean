import TypeIIIPublishedPhysicalConstruction
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The compact-lissity rule from finite-coefficient inputs

This module proves the finite-level induction and constructs the existing
`CohomologyRules` interface without taking its `compact_lisse` field as an input.
The underlying sheaves and the general cited rules remain explicit parameters.

Interpret the finite category as torsion sheaves on a fixed good compactification
of a relative curve. `residueAdmissible` includes the hypotheses of Laumon,
Semi-continuite du conducteur de Swan, section 2.1, for the extension by zero
of a constant-rank lisse residue sheaf. The conductor is computed after restriction
of scalars to the prime residue field. Higher quotients are NOT declared to have
field coefficients: their universal local acyclicity is deduced using actual
short exact sequences in the supplied category.

The passage to integral coefficients is the one in Hansen--Scholze, Relative
perversity, proof of Proposition 3.8; proper pushforward preserves ULA by the
discussion after Proposition 3.3. The final lissity rule includes rationalization,
degree-one cohomology and its identification with the original compact functor.
No existence of such a common sheaf realization is asserted here.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients

open PublishedPhysicalConstruction

universe u v w z a b

/-- Finite coefficient objects for one fixed compactified relative curve. -/
structure FiniteData (F : Type a) (Point : Type v) where
  residueAdmissible : F → Prop
  boundaryConductor : F → Point → ℕ
  ULA : F → Prop

/-- Only the residue-field criterion and extension stability are supplied.
The latter is the exact-triangle property of vanishing cycles. -/
structure FiniteRules {F : Type a} {Point : Type v}
    [Category.{b} F] [Abelian F] (T : FiniteData F Point) : Prop where
  conductor_ula : ∀ B, T.residueAdmissible B →
    (∃ N : ℕ, ∀ t, T.boundaryConductor B t = N) → T.ULA B
  extension_ula : ∀ S : ShortComplex F, S.ShortExact →
    T.ULA S.X₁ → T.ULA S.X₃ → T.ULA S.X₂

/-- Levels are j_! of lattice quotients by powers of a uniformizer.
`step A n` is the original sequence
0 → L/varpi → L/varpi^(n+2) → L/varpi^(n+1) → 0.
All three objects are recorded explicitly; the morphisms and their exactness
are part of the lattice model, not replaced by dimension comparisons. -/
structure LatticeData (Input : Type u) {F : Type a}
    [Category.{b} F] [Abelian F] where
  level : Input → ℕ → F
  residueDegree : Input → ℕ
  step : Input → ℕ → ShortComplex F
  step_first : ∀ A n, (step A n).X₁ = level A 1
  step_middle : ∀ A n, (step A n).X₂ = level A (n + 2)
  step_last : ∀ A n, (step A n).X₃ = level A (n + 1)

/-- Standard lattice facts to match with the chosen actual model.
Conductor reduction includes the degree of restriction of residue scalars;
neither lissity of compact cohomology nor ULA is supplied here. -/
structure LatticeRules {Input : Type u} {Point : Type v} {F : Type a}
    [Category.{b} F] [Abelian F] (D : CurveData Input Point)
    (T : FiniteData F Point) (M : LatticeData Input (F := F)) : Prop where
  residue_admissible : ∀ A, D.Lisse A → T.residueAdmissible (M.level A 1)
  residue_degree_pos : ∀ A, D.Lisse A → 0 < M.residueDegree A
  residue_conductor : ∀ A, D.Lisse A → ∀ t,
    T.boundaryConductor (M.level A 1) t = M.residueDegree A *
      ((D.rank A + D.swanZero A t) + (D.rank A + D.swanInfinity A t))
  step_exact : ∀ A, D.Lisse A → ∀ n, (M.step A n).ShortExact

/-- General integral passage and proper ULA pushforward, with the original
compact functor retained. `integralULA A` concerns j_! of the chosen lattice. -/
structure AdicRules {Input : Type u} {Point : Type v} {F : Type a}
    {C : Type w} [Category.{b} F] [Abelian F] [Category.{z} C]
    (D : CurveData Input Point) (H : CohomologyData Input C)
    (P : ParameterData C) (T : FiniteData F Point)
    (M : LatticeData Input (F := F)) where
  integralULA : Input → Prop
  integral_of_levels : ∀ A, D.Lisse A →
    (∀ n : ℕ, T.ULA (M.level A (n + 1))) → integralULA A
  proper_lisse : ∀ A, D.Lisse A → integralULA A → P.Lisse (H.compact A)

section Derivation

variable {Input : Type u} {Point : Type v} {F : Type a} {C : Type w}
  [Category.{b} F] [Abelian F] [Category.{z} C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  {T : FiniteData F Point} {M : LatticeData Input (F := F)}
  (finite : FiniteRules T) (lattice : LatticeRules D T M)
  (adic : AdicRules D H P T M)

include lattice

theorem residue_conductor_constant (A : Input) (hA : D.Lisse A)
    (hN : ∃ N : ℕ, ∀ t, (D.rank A + D.swanZero A t) +
      (D.rank A + D.swanInfinity A t) = N) :
    ∃ N : ℕ, ∀ t, T.boundaryConductor (M.level A 1) t = N := by
  obtain ⟨N, hN⟩ := hN
  exact ⟨M.residueDegree A * N, fun t =>
    (lattice.residue_conductor A hA t).trans (congrArg (M.residueDegree A * ·) (hN t))⟩

include finite

/-- Higher residue-power quotients use extensions, never a field-coefficient
conductor theorem applied to a nonfield ring. -/
theorem all_positive_levels_ula (A : Input) (hA : D.Lisse A)
    (hN : ∃ N : ℕ, ∀ t, (D.rank A + D.swanZero A t) +
      (D.rank A + D.swanInfinity A t) = N) :
    ∀ n : ℕ, T.ULA (M.level A (n + 1)) := by
  have hOne : T.ULA (M.level A 1) := finite.conductor_ula _
    (lattice.residue_admissible A hA) (residue_conductor_constant lattice A hA hN)
  intro n
  induction n with
  | zero => exact hOne
  | succ n ih =>
    have hFirst : T.ULA (M.step A n).X₁ := by rw [M.step_first]; exact hOne
    have hLast : T.ULA (M.step A n).X₃ := by rw [M.step_last]; exact ih
    have h := finite.extension_ula (M.step A n) (lattice.step_exact A hA n) hFirst hLast
    simpa only [M.step_middle, Nat.succ_eq_add_one] using h

include adic

/-- The existing compact-lissity rule is a conclusion from finite inputs. -/
theorem compact_lisse (A : Input) (hA : D.Lisse A)
    (hN : ∃ N : ℕ, ∀ t, (D.rank A + D.swanZero A t) +
      (D.rank A + D.swanInfinity A t) = N) : P.Lisse (H.compact A) :=
  adic.proper_lisse A hA (adic.integral_of_levels A hA
    (all_positive_levels_ula finite lattice A hA hN))

/-- Both literal Type III inputs satisfy the finite criterion with conductor 27. -/
theorem input_and_dual_compact_lisse (K : KloostermanInputData D) (R : CurveRules D) :
    P.Lisse (H.compact K.input) ∧ P.Lisse (H.compact (D.dual K.input)) :=
  ⟨compact_lisse finite lattice adic K.input (K.input_lisse R) ⟨27, K.input_conductor R⟩,
    compact_lisse finite lattice adic (D.dual K.input)
      (R.dual_lisse _ (K.input_lisse R)) ⟨27, K.dual_input_conductor R⟩⟩

end Derivation

/-- The other existing cohomology rules, with the conductor-to-lissity
conclusion omitted. These are still explicit external theory inputs. -/
structure OtherCohomologyRules {Input : Type u} {Point : Type v}
    {C : Type w} [Category.{z} C] [Abelian C]
    (D : CurveData Input Point) (H : CohomologyData Input C)
    (P : ParameterData C) : Prop where
  ordinary_duality : ∀ A, D.Lisse A → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact (D.dual A)) →
    Nonempty (H.ordinary A ≅ P.dualTateMinusOne (H.compact (D.dual A)))
  dualTate_lisse : ∀ A, P.Lisse A → P.Lisse (P.dualTateMinusOne A)
  lisse_of_iso : ∀ A B, Nonempty (A ≅ B) → P.Lisse B → P.Lisse A
  image_lisse : ∀ A B (f : A ⟶ B), P.Lisse A → P.Lisse B → P.Lisse (Abelian.image f)
  image_pure : ∀ A a, D.Lisse A → D.Pure A a →
    D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact A) → P.Lisse (H.compact (D.dual A)) →
    P.Pure (parabolicCore H A) (a + 1)
  signed_lisse : ∀ A, P.Lisse A → P.Lisse (P.signed A)
  signed_pure : ∀ A a, P.Pure A a → P.Pure (P.signed A) a
  dualTate_pure : ∀ A a, P.Lisse A → P.Pure A a →
    P.Pure (P.dualTateMinusOne A) (2 - a)

/-- Adapter into the unchanged source interface. No complete CohomologyRules
or compact-lissity premise is required as an argument. -/
theorem cohomologyRules {Input : Type u} {Point : Type v} {F : Type a} {C : Type w}
    [Category.{b} F] [Abelian F] [Category.{z} C] [Abelian C]
    {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
    {T : FiniteData F Point} {M : LatticeData Input (F := F)}
    (finite : FiniteRules T) (lattice : LatticeRules D T M)
    (adic : AdicRules D H P T M) (other : OtherCohomologyRules D H P) :
    CohomologyRules D H P := {
  compact_lisse := compact_lisse finite lattice adic
  ordinary_duality := other.ordinary_duality
  dualTate_lisse := other.dualTate_lisse
  lisse_of_iso := other.lisse_of_iso
  image_lisse := other.image_lisse
  image_pure := other.image_pure
  signed_lisse := other.signed_lisse
  signed_pure := other.signed_pure
  dualTate_pure := other.dualTate_pure
}

end PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients

#print axioms PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients.residue_conductor_constant
#print axioms PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients.all_positive_levels_ula
#print axioms PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients.compact_lisse
#print axioms PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients.input_and_dual_compact_lisse
#print axioms PrimeGap182.TypeIII.CompactLissityFromFiniteCoefficients.cohomologyRules
