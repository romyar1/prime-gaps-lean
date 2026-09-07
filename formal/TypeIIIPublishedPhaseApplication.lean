import TypeIIIFuTensorApplication
import Mathlib.RepresentationTheory.FDRep
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Conditional application of generic local Fourier laws

The linear objects, direct sums, tensor products and equivariant maps are
actual Mathlib finite-dimensional representations.  Their phase observables
and the general local Fourier laws remain explicit hypotheses.  The generic
Fu law concerns arbitrary cubic blocks and does not mention the correlation,
rectangle parameters, or the final allowed phase set.

`CoreLocalData` is separate application data: the actual Mackey/local-Fourier
comparison, the finite-origin equivariant maps, exactness, and the core rank.
This file does not construct those geometric maps or call that application
data a published theorem.  From them it proves rank exhaustion, the generic
scalar substitution, and tensor phase containment.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.PublishedPhaseApplication

universe u v w

abbrev PhaseField (K : Type u) [Field K] := AlgebraicClosure (RatFunc K)

variable {K : Type u} [Field K]

theorem phaseField_map_C (c : K) :
    algebraMap (RatFunc K) (PhaseField K) (RatFunc.C c) =
      algebraMap K (PhaseField K) c := by
  rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]

/-- The actual transcendental angular coordinate. -/
def direction (K : Type u) [Field K] : PhaseField K :=
  algebraMap (RatFunc K) (PhaseField K) RatFunc.X

theorem direction_ne_zero : direction K ≠ 0 := by
  simpa only [direction, map_zero] using
    (algebraMap (RatFunc K) (PhaseField K)).injective.ne RatFunc.X_ne_zero

theorem direction_pow_ne_constant (d : ℕ) (hd : 0 < d) (c : K) :
    direction K ^ d ≠ algebraMap K (PhaseField K) c := by
  have hrat : (RatFunc.X : RatFunc K) ^ d - RatFunc.C c ≠ 0 := by
    simpa only [map_sub, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (Polynomial.X_pow_sub_C_ne_zero hd c)
  have hnonzero : algebraMap (RatFunc K) (PhaseField K)
      (RatFunc.X ^ d - RatFunc.C c) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap (RatFunc K) (PhaseField K)).injective.ne hrat
  intro h
  apply hnonzero
  rw [map_sub, map_pow]
  change direction K ^ d - algebraMap (RatFunc K) (PhaseField K) (RatFunc.C c) = 0
  rw [← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply, h, sub_self]

/-- A generic cubic branch cannot be the exceptional branch q=1. -/
theorem generic_cubic_branch_ne_one (c : K) (q : PhaseField K)
    (hq : q ^ 3 = algebraMap K (PhaseField K) c / direction K ^ 3) : q ≠ 1 := by
  intro h
  rw [h, one_pow] at hq
  have he := (eq_div_iff (pow_ne_zero _ direction_ne_zero)).mp hq
  exact direction_pow_ne_constant 3 (by omega) c (by simpa only [one_mul] using he)

/-- In the substitution ξ=T²/A, this A equals αz/m. -/
def radialScale (α m : K) : PhaseField K :=
  algebraMap K (PhaseField K) α * direction K / algebraMap K (PhaseField K) m

theorem radialScale_ne_zero (α m : K) (hα : α ≠ 0) (hm : m ≠ 0) :
    radialScale α m ≠ 0 := by
  apply div_ne_zero
  · apply mul_ne_zero
    · simpa only [map_zero] using (algebraMap K (PhaseField K)).injective.ne hα
    · exact direction_ne_zero
  · simpa only [map_zero] using (algebraMap K (PhaseField K)).injective.ne hm

/-- Fu's arbitrary-q square relation becomes the literal per-entry
relation after the actual transcendental change of variables. -/
theorem fuCubicSquaredPhase_of_generic_square [IsAlgClosed K]
    (α m n : K) (q β : PhaseField K)
    (hq : q ^ 3 = algebraMap K (PhaseField K) (m / n) / direction K ^ 3)
    (hβ : β ^ 2 = 4 * radialScale α m * (q - 1) ^ 3) :
    FuCubicSquaredPhase α m n β := by
  obtain ⟨γ, hγ, heq⟩ :=
    (generic_cubic_roots_iff (m / n) q (direction K) direction_ne_zero).mp hq
  refine ⟨γ, hγ, hβ.trans ?_⟩
  rw [heq]
  calc
    _ = (4 * algebraMap K (PhaseField K) α / algebraMap K (PhaseField K) m) *
        (algebraMap K (PhaseField K) γ - direction K) ^ 3 / direction K ^ 2 := by
      simpa only [radialScale, mul_div_assoc, mul_assoc] using
        fu_phase_square_substitution (algebraMap K (PhaseField K) α)
          (algebraMap K (PhaseField K) m) (algebraMap K (PhaseField K) γ)
          (direction K) direction_ne_zero
    _ = _ := by
      dsimp only [fuRadialPhaseSquare]
      change _ = algebraMap (RatFunc K) (PhaseField K)
        (RatFunc.C (4 * α / m) * (RatFunc.C γ - RatFunc.X) ^ 3 / RatFunc.X ^ 2)
      simp only [map_div₀, map_mul, map_pow, map_sub, phaseField_map_C, map_ofNat, direction]

variable {E : Type v} [Field E] {G : Type w} [Group G]

/-- The literal finite direct sum of representations. -/
def finiteSum {ι : Type} [Fintype ι] (R : ι → FDRep E G) : FDRep E G :=
  FDRep.of (Representation.directSum fun i => (R i).ρ)

theorem finiteSum_finrank {ι : Type} [Fintype ι] (R : ι → FDRep E G) :
    Module.finrank E (finiteSum R) = ∑ i, Module.finrank E (R i) := by
  change Module.finrank E (DirectSum ι (fun i => (R i).V)) = _
  exact Module.finrank_directSum (R := E) (ι := ι) (fun i => (R i).V)

/-- The literal tensor product of the representations at the selected
indices, with its diagonal group action. -/
def selectedTensor {ι : Type} (s : Finset ι) (R : ι → FDRep E G) : FDRep E G :=
  FDRep.of ({
    toFun g := PiTensorProduct.map (fun i : s => (R i.val).ρ g)
    map_one' := by simp only [map_one, PiTensorProduct.map_one]
    map_mul' g h := by simp only [map_mul, PiTensorProduct.map_mul]
  } : Representation E G (PiTensorProduct E (fun i : s => (R i.val).V)))

/-- The actual contragredient representation. Unramified twists are
invisible after restriction to wild inertia. -/
def dualRepresentation (R : FDRep E G) : FDRep E G :=
  FDRep.of (Representation.dual R.ρ)

/-- An actual representation subquotient, witnessed by equivariant
injective and surjective linear maps. -/
def IsSubquotient (A B : FDRep E G) : Prop :=
  ∃ W : FDRep E G, ∃ i : Representation.IntertwiningMap W.ρ B.ρ,
    ∃ q : Representation.IntertwiningMap W.ρ A.ρ,
      Function.Injective i ∧ Function.Surjective q

/-- Observables of pole-one wild representations at the radial origin
after t=T², whose characters are AS(β/T), with coefficient zero
reserved for the trivial wild character.  Their realization is explicit
external data, not a declaration that arbitrary representations have such
a profile. -/
structure PhaseData (K : Type u) [Field K] (E : Type v) [Field E]
    (G : Type w) [Group G] where
  HasProfile : FDRep E G → Prop
  phases : FDRep E G → Set (PhaseField K)

/-- General finite-dimensional character laws.  In the intended model
these express exactness on fully decomposed wild inertia and the character
sum law for the actual tensor product. -/
structure PhaseRules [CharZero E] (D : PhaseData K E G) : Prop where
  transport : ∀ A B : FDRep E G, ∀ f : Representation.IntertwiningMap A.ρ B.ρ,
    Function.Bijective f →
      (D.HasProfile A ↔ D.HasProfile B) ∧ D.phases A = D.phases B
  sum_profile : ∀ {ι : Type} [Fintype ι], ∀ R : ι → FDRep E G,
    (∀ i, D.HasProfile (R i)) → D.HasProfile (finiteSum R)
  sum_phases : ∀ {ι : Type} [Fintype ι], ∀ R : ι → FDRep E G,
    (∀ i, D.HasProfile (R i)) →
      ∀ β ∈ D.phases (finiteSum R), ∃ i, β ∈ D.phases (R i)
  tensor_profile : ∀ {ι : Type}, ∀ s : Finset ι, ∀ R : ι → FDRep E G,
    (∀ i ∈ s, D.HasProfile (R i)) → D.HasProfile (selectedTensor s R)
  tensor_phases : ∀ {ι : Type}, ∀ s : Finset ι, ∀ R : ι → FDRep E G,
    (∀ i ∈ s, D.HasProfile (R i)) →
      ∀ β ∈ D.phases (selectedTensor s R),
        ∃ b : ι → PhaseField K, (∀ i ∈ s, b i ∈ D.phases (R i)) ∧ β = ∑ i ∈ s, b i
  dual_profile : ∀ R : FDRep E G, D.HasProfile R → D.HasProfile (dualRepresentation R)
  dual_phases : ∀ R : FDRep E G, D.HasProfile R →
    ∀ β ∈ D.phases (dualRepresentation R), -β ∈ D.phases R
  subquotient_profile : ∀ A B : FDRep E G, IsSubquotient A B →
    D.HasProfile B → D.HasProfile A
  subquotient_phases : ∀ A B : FDRep E G, IsSubquotient A B →
    D.HasProfile B → D.phases A ⊆ D.phases B
  map_to_trivial_zero : ∀ A B : FDRep E G,
    D.HasProfile A → (0 : PhaseField K) ∉ D.phases A →
    Representation.IsTrivial B.ρ →
      ∀ f : Representation.IntertwiningMap A.ρ B.ρ, f.toLinearMap = 0

/-- The operation is the infinity-to-zero local Fourier transform of
[3]_*AS(3(1-q)x), pulled back by ξ=T²/A, then restricted to wild inertia at T=0.
It is supplied separately from the theorem governing that operation. -/
structure CubicFourierData (K : Type u) [Field K] (E : Type v) [Field E]
    (G : Type w) [Group G] where
  output : PhaseField K → PhaseField K → FDRep E G

/-- Fu Theorem 0.1(iii), r=3,s=1, as a generic wild-profile rule. The
arithmetic application and its Mackey comparison are not fields here.
The intended compatible ℓ-adic realization of the characteristic-zero
coefficient field is separate data; this is not an assertion for all fields. -/
structure FuRules [CharZero E] (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : PhaseData K E G) (C : CubicFourierData K E G) : Prop where
  formula : 3 < p → ∀ A q : PhaseField K, A ≠ 0 → q ≠ 1 →
    D.HasProfile (C.output A q) ∧ Module.finrank E (C.output A q) = 2 ∧
      ∀ β ∈ D.phases (C.output A q), β ^ 2 = 4 * A * (q - 1) ^ 3

/-- Separate actual application data. The Mackey comparison is an
equivalence of representations, not merely a list of six candidate phases.
The finite-origin map has the direction H→V. No phase containment is a field. -/
structure CoreLocalData (C : CubicFourierData K E G)
    (α m n : K) (H : FDRep E G) where
  q : Fin 3 → PhaseField K
  q_cube : ∀ i, q i ^ 3 = algebraMap K (PhaseField K) (m / n) / direction K ^ 3
  V : FDRep E G
  T : FDRep E G
  mackeyFourierComparison : Representation.Equiv V.ρ
    (finiteSum (fun i => C.output (radialScale α m) (q i))).ρ
  toVanishing : Representation.IntertwiningMap H.ρ V.ρ
  toTame : Representation.IntertwiningMap V.ρ T.ρ
  exact : LinearMap.range toVanishing.toLinearMap = LinearMap.ker toTame.toLinearMap
  tame : Representation.IsTrivial T.ρ
  core_rank : Module.finrank E H = 6

variable [CharZero E] {p : ℕ} [Fact p.Prime] [CharP K p]
  {D : PhaseData K E G} {C : CubicFourierData K E G}

/-- A nonexceptional cubic block has no trivial wild character. This is
deduced from the generic squared-phase formula, rather than assumed for
the correlation core. -/
theorem cubic_output_zero_not_phase (F : FuRules p D C) (hp : 3 < p)
    (h2 : (2 : K) ≠ 0) (A q : PhaseField K) (hA : A ≠ 0) (hq : q ≠ 1) :
    (0 : PhaseField K) ∉ D.phases (C.output A q) := by
  have hfourK : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) ^ 2 = 4 by ring] using pow_ne_zero 2 h2
  have hfour : (4 : PhaseField K) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (algebraMap K (PhaseField K)).injective.ne hfourK
  intro hzero
  have heq := (F.formula hp A q hA hq).2.2 0 hzero
  have hn : 4 * A * (q - 1) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hfour hA) (pow_ne_zero 3 (sub_ne_zero.mpr hq))
  exact hn (by simpa only [zero_pow (by decide : 2 ≠ 0)] using heq.symm)

/-- The original finite-origin map exhausts the core. Its surjectivity
comes from exactness and the vanishing of the map to the tame target;
its injectivity follows from the proved six-dimensional target and the
supplied rank of the actual core. Consequently every core phase satisfies
the literal Fu scalar equation. -/
theorem core_profile_of_local_data [IsAlgClosed K]
    (R : PhaseRules D) (F : FuRules p D C) (hp : 3 < p) (h2 : (2 : K) ≠ 0)
    (α m n : K) (hα : α ≠ 0) (hm : m ≠ 0)
    (H : FDRep E G) (A : CoreLocalData C α m n H) :
    D.HasProfile H ∧ ∀ β ∈ D.phases H, FuCubicSquaredPhase α m n β := by
  let B : Fin 3 → FDRep E G := fun i => C.output (radialScale α m) (A.q i)
  have hscale := radialScale_ne_zero α m hα hm
  have hq (i : Fin 3) : A.q i ≠ 1 :=
    generic_cubic_branch_ne_one (m / n) (A.q i) (A.q_cube i)
  have hFu (i : Fin 3) := F.formula hp (radialScale α m) (A.q i) hscale (hq i)
  have hBp (i : Fin 3) : D.HasProfile (B i) := (hFu i).1
  have hsum := R.sum_profile B hBp
  have hcomparison := R.transport A.V (finiteSum B)
    A.mackeyFourierComparison.toIntertwiningMap
    A.mackeyFourierComparison.toLinearEquiv.bijective
  have hVp : D.HasProfile A.V := hcomparison.1.mpr hsum
  have hVzero : (0 : PhaseField K) ∉ D.phases A.V := by
    intro hzero
    rw [hcomparison.2] at hzero
    obtain ⟨i, hi⟩ := R.sum_phases B hBp 0 hzero
    exact cubic_output_zero_not_phase F hp h2 (radialScale α m) (A.q i)
      hscale (hq i) hi
  have hVrank : Module.finrank E A.V = 6 := by
    calc
      Module.finrank E A.V = Module.finrank E (finiteSum B) :=
        A.mackeyFourierComparison.toLinearEquiv.finrank_eq
      _ = ∑ i : Fin 3, Module.finrank E (B i) := finiteSum_finrank B
      _ = ∑ _i : Fin 3, (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hFu i).2.1
      _ = 6 := by norm_num
  have hmapzero := R.map_to_trivial_zero A.V A.T hVp hVzero A.tame A.toTame
  have hbij := localFourier_exhaustion_of_exact_rank
    A.toVanishing.toLinearMap A.toTame.toLinearMap A.exact hmapzero
    (A.core_rank.trans hVrank.symm)
  have hcore := R.transport H A.V A.toVanishing hbij
  refine ⟨hcore.1.mpr hVp, ?_⟩
  intro β hβ
  rw [hcore.2, hcomparison.2] at hβ
  obtain ⟨i, hi⟩ := R.sum_phases B hBp β hβ
  exact fuCubicSquaredPhase_of_generic_square α m n (A.q i) β
    (A.q_cube i) ((hFu i).2.2 β hi)

/-- Select the actual core or its contragredient. -/
def signedRepresentation (dual : Bool) (H : FDRep E G) : FDRep E G :=
  if dual then dualRepresentation H else H

/-- Contragredient characters negate their pole coefficient. Their
squares, and hence membership in the scalar Fu relation, are unchanged. -/
theorem core_or_dual_profile [IsAlgClosed K]
    (R : PhaseRules D) (F : FuRules p D C) (hp : 3 < p) (h2 : (2 : K) ≠ 0)
    (α m n : K) (hα : α ≠ 0) (hm : m ≠ 0)
    (H : FDRep E G) (A : CoreLocalData C α m n H) (dual : Bool) :
    D.HasProfile (signedRepresentation dual H) ∧
      ∀ β ∈ D.phases (signedRepresentation dual H), FuCubicSquaredPhase α m n β := by
  have hcore := core_profile_of_local_data R F hp h2 α m n hα hm H A
  cases dual with
  | false => exact hcore
  | true =>
    change D.HasProfile (dualRepresentation H) ∧ _
    refine ⟨R.dual_profile H hcore.1, ?_⟩
    intro β hβ
    obtain ⟨γ, hγ, heq⟩ := hcore.2 (-β) (R.dual_phases H hcore.1 β hβ)
    exact ⟨γ, hγ, by simpa only [neg_sq] using heq⟩

/-- The literal tensor of any selected cores and contragredients has only
the independently proved rectangle phases. No rectangle phase bound or
constituent exclusion is assumed. -/
theorem rectangle_tensor_profile [IsAlgClosed K]
    (R : PhaseRules D) (F : FuRules p D C) (hp : 3 < p) (h2 : (2 : K) ≠ 0)
    (α : K) (hα : α ≠ 0) (m n : Fin 2 → K) (hm : ∀ i, m i ≠ 0)
    (s : Finset PhaseRectangle) (H : PhaseRectangle → FDRep E G)
    (dual : PhaseRectangle → Bool)
    (data : ∀ e ∈ s, CoreLocalData C α (m e.1) (n e.2) (H e)) :
    D.HasProfile (selectedTensor s (fun e => signedRepresentation (dual e) (H e))) ∧
      D.phases (selectedTensor s (fun e => signedRepresentation (dual e) (H e))) ⊆
        rectangleAllowedPhases α m n s := by
  have hentry (e : PhaseRectangle) (he : e ∈ s) :=
    core_or_dual_profile R F hp h2 α (m e.1) (n e.2) hα (hm e.1)
      (H e) (data e he) (dual e)
  have htensor := R.tensor_profile s (fun e => signedRepresentation (dual e) (H e))
    (fun e he => (hentry e he).1)
  refine ⟨htensor, ?_⟩
  intro β hβ
  obtain ⟨b, hb, heq⟩ := R.tensor_phases s
    (fun e => signedRepresentation (dual e) (H e))
    (fun e he => (hentry e he).1) β hβ
  rw [heq]
  exact sum_mem_rectangleAllowedPhases_of_fuSquaredPhases h2 α hα m n hm s b
    (fun e he => (hentry e he).2 (b e) (hb e he))

/-- An actual equivariant subquotient inherits the proved tensor profile
and containment. Relating a geometric radial representation to this
subquotient is still explicitly separate application data. -/
theorem subquotient_rectangle_profile [IsAlgClosed K]
    (R : PhaseRules D) (F : FuRules p D C) (hp : 3 < p) (h2 : (2 : K) ≠ 0)
    (α : K) (hα : α ≠ 0) (m n : Fin 2 → K) (hm : ∀ i, m i ≠ 0)
    (s : Finset PhaseRectangle) (H : PhaseRectangle → FDRep E G)
    (dual : PhaseRectangle → Bool)
    (data : ∀ e ∈ s, CoreLocalData C α (m e.1) (n e.2) (H e))
    (A : FDRep E G)
    (hA : IsSubquotient A
      (selectedTensor s (fun e => signedRepresentation (dual e) (H e)))) :
    D.HasProfile A ∧ D.phases A ⊆ rectangleAllowedPhases α m n s := by
  have htensor := rectangle_tensor_profile R F hp h2 α hα m n hm s H dual data
  exact ⟨R.subquotient_profile A _ hA htensor.1,
    (R.subquotient_phases A _ hA htensor.1).trans htensor.2⟩

end PrimeGap182.TypeIII.PublishedPhaseApplication

#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseField
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.phaseField_map_C
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.direction
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.direction_ne_zero
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.direction_pow_ne_constant
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.generic_cubic_branch_ne_one
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.radialScale
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.radialScale_ne_zero
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.fuCubicSquaredPhase_of_generic_square
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.finiteSum
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.finiteSum_finrank
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.selectedTensor
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.dualRepresentation
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.IsSubquotient
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.FuRules
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.cubic_output_zero_not_phase
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.core_profile_of_local_data
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.signedRepresentation
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.core_or_dual_profile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.rectangle_tensor_profile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.subquotient_rectangle_profile


/- Generated structure declarations are included in the axiom audit. -/
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.T
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.V
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.core_rank
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.exact
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.mackeyFourierComparison
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.q
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.q_cube
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.tame
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.toTame
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CoreLocalData.toVanishing
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.output
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.CubicFourierData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.FuRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.FuRules.formula
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.FuRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.FuRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.FuRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.HasProfile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.phases
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.dual_phases
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.dual_profile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.map_to_trivial_zero
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.subquotient_phases
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.subquotient_profile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.sum_phases
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.sum_profile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.tensor_phases
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.tensor_profile
#print axioms PrimeGap182.TypeIII.PublishedPhaseApplication.PhaseRules.transport
