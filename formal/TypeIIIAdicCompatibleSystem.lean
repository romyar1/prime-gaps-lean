import TypeIIIAdicCompletionRangeDescent
import Mathlib.LinearAlgebra.Pi

/-!
# The original completion map into a compatible module system

Let the n-th target module be annihilated by I^(n+1), with specified
linear transition maps and a compatible family of maps from M. Each
original map factors through M/I^(n+1)M. Composing that factor with the
original completion evaluation gives a compatible family, hence an
actual linear map into the submodule of compatible sequences.

Every coordinate retains the original map on M. No finite-generation,
Noetherian, completeness, or surjectivity premise is used to construct
the map. Finite generation of I is used only in the final uniqueness
theorem. No comparison isomorphism or geometric formal-functions
theorem is asserted. The coefficient, source, and target universes are
independent.
-/

noncomputable section

universe u v w

namespace PrimeGap182.TypeIII.AdicCompatibleSystem

/-- A system with its specified linear transitions, including their actual identity
and composition laws. -/
structure System (R : Type u) [CommRing R] (B : ℕ → Type w)
    [∀ n : ℕ, AddCommGroup (B n)] [∀ n : ℕ, Module R (B n)] where
  transition : ∀ {m n : ℕ}, m ≤ n → B n →ₗ[R] B m
  transition_refl : ∀ n : ℕ, transition (le_refl n) = LinearMap.id
  transition_comp : ∀ {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n),
    (transition hkm).comp (transition hmn) = transition (hkm.trans hmn)

variable {R : Type u} [CommRing R] {B : ℕ → Type w}
  [∀ n : ℕ, AddCommGroup (B n)] [∀ n : ℕ, Module R (B n)]

/-- The literal submodule of families compatible under every specified transition. -/
def compatibleSubmodule (S : System R B) : Submodule R (∀ n : ℕ, B n) where
  carrier := { b | ∀ {m n : ℕ} (hmn : m ≤ n), S.transition hmn (b n) = b m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, hf hmn]

/-- Compatible sequences in the original target modules. -/
abbrev Sections (S : System R B) : Type w := ↥(compatibleSubmodule S)

/-- The original coordinate projection from a compatible sequence. -/
def projection (S : System R B) (n : ℕ) : Sections S →ₗ[R] B n :=
  (LinearMap.proj n).comp (compatibleSubmodule S).subtype

/-- The projection is literal evaluation of the stored sequence. -/
theorem projection_apply (S : System R B) (n : ℕ) (b : Sections S) :
    projection S n b = b.val n := rfl

/-- Equality of all original coordinates is equality of compatible sequences. -/
@[ext]
theorem sections_ext (S : System R B) {x y : Sections S}
    (h : ∀ n : ℕ, projection S n x = projection S n y) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

/-- The coordinate projections obey the specified original transitions. -/
theorem projection_transition (S : System R B) {m n : ℕ} (hmn : m ≤ n) :
    (S.transition hmn).comp (projection S n) = projection S m := by
  ext b
  exact b.property hmn

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The original compatible family, as a map into the literal submodule of sequences. -/
def originalMap (S : System R B) (σ : ∀ n : ℕ, M →ₗ[R] B n)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m) :
    M →ₗ[R] Sections S where
  toFun a := ⟨fun n => σ n a, fun hmn => LinearMap.congr_fun (hσ hmn) a⟩
  map_add' a b := by
    apply Subtype.ext
    funext n
    exact (σ n).map_add a b
  map_smul' r a := by
    apply Subtype.ext
    funext n
    exact (σ n).map_smul r a

/-- The original compatible-family map has the original coordinate maps. -/
theorem originalMap_apply (S : System R B) (σ : ∀ n : ℕ, M →ₗ[R] B n)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (a : M) (n : ℕ) :
    projection S n (originalMap S σ hσ a) = σ n a := rfl

variable (I : Ideal R) (σ : ∀ n : ℕ, M →ₗ[R] B n)
  (ann : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (B n)) = ⊥)

include ann in
/-- The target annihilator proves that the original map kills the required source submodule. -/
theorem pow_smul_le_ker (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R M) ≤ (σ n).ker := by
  refine Submodule.smul_le.mpr ?_
  intro r hr a _ha
  rw [LinearMap.mem_ker, map_smul]
  have hz : r • σ n a ∈ I ^ (n + 1) • (⊤ : Submodule R (B n)) :=
    Submodule.smul_mem_smul hr Submodule.mem_top
  simpa only [ann n, Submodule.mem_bot] using hz

/-- The quotient factor of the original n-th map, constructed by the quotient universal property. -/
def sigmaBar (n : ℕ) : M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) →ₗ[R] B n :=
  (I ^ (n + 1) • (⊤ : Submodule R M)).liftQ (σ n) (pow_smul_le_ker I σ ann n)

/-- The quotient factor retains the original map on each original representative. -/
theorem sigmaBar_mkQ (n : ℕ) :
    (sigmaBar I σ ann n).comp (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ = σ n :=
  Submodule.liftQ_mkQ _ _ _

/-- The n-th completion coordinate uses the original evaluation at n+1. -/
def completionCoordinate (n : ℕ) : AdicCompletion I M →ₗ[R] B n :=
  (sigmaBar I σ ann n).comp (AdicCompletion.eval I M (n + 1))

/-- On an original element, the completion coordinate is the original n-th map. -/
theorem completionCoordinate_of (n : ℕ) (a : M) :
    completionCoordinate I σ ann n (AdicCompletion.of I M a) = σ n a := rfl

/-- The completion coordinate extends the original map along the original completion map. -/
theorem completionCoordinate_comp_of (n : ℕ) :
    (completionCoordinate I σ ann n).comp (AdicCompletion.of I M) = σ n := by
  ext a
  exact completionCoordinate_of I σ ann n a

/-- The quotient factors commute with the original transitions between source quotients. -/
theorem sigmaBar_transition (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    {m n : ℕ} (hmn : m ≤ n) :
    (S.transition hmn).comp (sigmaBar I σ ann n) =
      (sigmaBar I σ ann m).comp
        (AdicCompletion.transitionMap I M (Nat.succ_le_succ hmn)) := by
  apply Submodule.linearMap_qext
  ext a
  change S.transition hmn (σ n a) = σ m a
  exact LinearMap.congr_fun (hσ hmn) a

/-- Original completion evaluations and original quotient compatibility give target compatibility. -/
theorem completionCoordinate_transition (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    {m n : ℕ} (hmn : m ≤ n) :
    (S.transition hmn).comp (completionCoordinate I σ ann n) =
      completionCoordinate I σ ann m := by
  unfold completionCoordinate
  rw [← LinearMap.comp_assoc, sigmaBar_transition I σ ann S hσ hmn,
    LinearMap.comp_assoc, AdicCompletion.transitionMap_comp_eval]

/-- The canonical map from the original completion to the literal compatible-sequence submodule. -/
def completionMap (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m) :
    AdicCompletion I M →ₗ[R] Sections S where
  toFun x := ⟨fun n => completionCoordinate I σ ann n x,
    fun hmn => LinearMap.congr_fun (completionCoordinate_transition I σ ann S hσ hmn) x⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (completionCoordinate I σ ann n).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact (completionCoordinate I σ ann n).map_smul r x

/-- Projection of the canonical map is its specified completion coordinate. -/
theorem projection_completionMap (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m) (n : ℕ) :
    (projection S n).comp (completionMap I σ ann S hσ) =
      completionCoordinate I σ ann n := rfl

/-- The actual coordinate formula is quotient factor after the original completion evaluation. -/
theorem completionMap_eval (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (x : AdicCompletion I M) (n : ℕ) :
    projection S n (completionMap I σ ann S hσ x) =
      sigmaBar I σ ann n (AdicCompletion.eval I M (n + 1) x) := rfl

/-- The whole canonical map retains the original compatible family on M. -/
theorem completionMap_of (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m) (a : M) :
    completionMap I σ ann S hσ (AdicCompletion.of I M a) = originalMap S σ hσ a := by
  apply Subtype.ext
  funext n
  rfl

/-- The canonical map extends the original compatible family along the original completion map. -/
theorem completionMap_comp_of (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m) :
    (completionMap I σ ann S hσ).comp (AdicCompletion.of I M) = originalMap S σ hσ := by
  apply LinearMap.ext
  intro a
  exact completionMap_of I σ ann S hσ a

/-- With a finitely generated ideal, any linear extension of the same original family
equals the constructed map. This adds no existence or surjectivity premise. -/
theorem completionMap_unique (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hI : I.FG) (L : AdicCompletion I M →ₗ[R] Sections S)
    (hL : L.comp (AdicCompletion.of I M) = originalMap S σ hσ) :
    L = completionMap I σ ann S hσ := by
  apply LinearMap.ext
  intro x
  apply sections_ext
  intro n
  let D : AdicCompletion I M →ₗ[R] B n :=
    (projection S n).comp L - completionCoordinate I σ ann n
  obtain ⟨a, ha⟩ := adicCompletion_exists_original_preimage I (n + 1) D hI (ann n) x
  have hLa : projection S n (L (AdicCompletion.of I M a)) = σ n a :=
    congrArg (projection S n) (LinearMap.congr_fun hL a)
  have hDa : D (AdicCompletion.of I M a) = 0 := by
    change projection S n (L (AdicCompletion.of I M a)) -
      completionCoordinate I σ ann n (AdicCompletion.of I M a) = 0
    rw [hLa, completionCoordinate_of, sub_self]
  have hx : D x = 0 := ha.symm.trans hDa
  change projection S n (L x) = completionCoordinate I σ ann n x
  exact sub_eq_zero.mp hx

#print axioms System
#print axioms System.mk
#print axioms System.rec
#print axioms System.recOn
#print axioms System.casesOn
#print axioms System.noConfusionType
#print axioms System.noConfusion
#print axioms System.transition
#print axioms System.transition_refl
#print axioms System.transition_comp
#print axioms compatibleSubmodule
#print axioms Sections
#print axioms projection
#print axioms projection_apply
#print axioms sections_ext
#print axioms PrimeGap182.TypeIII.AdicCompatibleSystem.sections_ext_iff
#print axioms projection_transition
#print axioms originalMap
#print axioms originalMap_apply
#print axioms pow_smul_le_ker
#print axioms sigmaBar
#print axioms sigmaBar_mkQ
#print axioms completionCoordinate
#print axioms completionCoordinate_of
#print axioms completionCoordinate_comp_of
#print axioms sigmaBar_transition
#print axioms completionCoordinate_transition
#print axioms completionMap
#print axioms projection_completionMap
#print axioms completionMap_eval
#print axioms completionMap_of
#print axioms completionMap_comp_of
#print axioms completionMap_unique

end PrimeGap182.TypeIII.AdicCompatibleSystem
