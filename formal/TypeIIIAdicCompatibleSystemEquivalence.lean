import TypeIIIAdicCompatibleSystem

/-!
# Invertibility of the original compatible-system completion map

If every original quotient factor sigmaBar is bijective, the existing
completionMap is bijective. Its inverse is obtained by applying those
quotient inverses at each positive index. The omitted index zero is the
actual quotient M/I^0 M, which is subsingleton. Compatibility is proved
using the original quotient and system transitions.

The resulting linear equivalence has the original completionMap as its
linear map. No finite-generation, Noetherian, finite-module, completeness,
or geometric assumption is imposed. In particular this generic algebraic
result does not assert formal functions for a proper scheme.
-/

noncomputable section

universe u v w

namespace PrimeGap182.TypeIII.AdicCompatibleSystem

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {B : ℕ → Type w} [∀ n : ℕ, AddCommGroup (B n)] [∀ n : ℕ, Module R (B n)]
  (I : Ideal R)

/-- The actual index-zero quotient of the completion is subsingleton. -/
theorem zeroQuotient_subsingleton :
    Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
  have hzero : I ^ 0 • (⊤ : Submodule R M) = ⊤ := by simp
  rw [hzero]
  infer_instance

variable (σ : ∀ n : ℕ, M →ₗ[R] B n)
  (ann : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (B n)) = ⊥)

/-- The original quotient factor, equipped with its given bijectivity. -/
def sigmaBarEquiv (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (n : ℕ) :
    (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) ≃ₗ[R] B n :=
  LinearEquiv.ofBijective (sigmaBar I σ ann n) (hbij n)

/-- No quotient map is replaced when forming its linear equivalence. -/
theorem sigmaBarEquiv_toLinearMap
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (n : ℕ) :
    (sigmaBarEquiv I σ ann hbij n).toLinearMap = sigmaBar I σ ann n := rfl

/-- The candidate completion coordinates use zero at index zero and the
original quotient inverses at positive indices. -/
def inverseCoordinates (S : System R B)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S) :
    ∀ n : ℕ, M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  fun n => Nat.casesOn (motive := fun k => M ⧸ (I ^ k • (⊤ : Submodule R M))) n 0
    (fun k => (sigmaBarEquiv I σ ann hbij k).symm (projection S k b))

/-- The candidate's zeroth coordinate is the unique zero-quotient class. -/
theorem inverseCoordinates_zero (S : System R B)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S) :
    inverseCoordinates I σ ann S hbij b 0 = 0 := rfl

/-- Every positive coordinate uses the inverse of the original quotient factor. -/
theorem inverseCoordinates_succ (S : System R B)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S) (n : ℕ) :
    inverseCoordinates I σ ann S hbij b (n + 1) =
      (sigmaBarEquiv I σ ann hbij n).symm (projection S n b) := rfl

/-- These coordinates commute with the original transitions of the adic completion. -/
theorem inverseCoordinates_compatible (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S)
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn (inverseCoordinates I σ ann S hbij b n) =
      inverseCoordinates I σ ann S hbij b m := by
  cases m with
  | zero =>
    let := zeroQuotient_subsingleton (M := M) I
    exact Subsingleton.elim _ _
  | succ m =>
    cases n with
    | zero => exact (Nat.not_succ_le_zero m hmn).elim
    | succ n =>
      have hmn' : m ≤ n := Nat.le_of_succ_le_succ hmn
      apply (hbij m).1
      change sigmaBar I σ ann m
          (AdicCompletion.transitionMap I M hmn
            ((sigmaBarEquiv I σ ann hbij n).symm (projection S n b))) =
        sigmaBar I σ ann m ((sigmaBarEquiv I σ ann hbij m).symm (projection S m b))
      have ht := LinearMap.congr_fun (sigmaBar_transition I σ ann S hσ hmn')
        ((sigmaBarEquiv I σ ann hbij n).symm (projection S n b))
      calc
        _ = S.transition hmn'
            (sigmaBar I σ ann n ((sigmaBarEquiv I σ ann hbij n).symm (projection S n b))) :=
          ht.symm
        _ = S.transition hmn' (projection S n b) := by
          change S.transition hmn'
            ((sigmaBarEquiv I σ ann hbij n)
              ((sigmaBarEquiv I σ ann hbij n).symm (projection S n b))) = _
          rw [LinearEquiv.apply_symm_apply]
        _ = projection S m b := b.property hmn'
        _ = sigmaBar I σ ann m
            ((sigmaBarEquiv I σ ann hbij m).symm (projection S m b)) :=
          ((sigmaBarEquiv I σ ann hbij m).apply_symm_apply (projection S m b)).symm

/-- The constructed compatible coordinates are an element of the original adic completion. -/
def completionPreimage (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S) :
    AdicCompletion I M :=
  ⟨inverseCoordinates I σ ann S hbij b,
    fun hmn => inverseCoordinates_compatible I σ ann S hσ hbij b hmn⟩

/-- The original completion map sends the constructed preimage to the prescribed family. -/
theorem completionMap_preimage (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S) :
    completionMap I σ ann S hσ (completionPreimage I σ ann S hσ hbij b) = b := by
  apply sections_ext
  intro n
  change sigmaBar I σ ann n
    ((sigmaBarEquiv I σ ann hbij n).symm (projection S n b)) = projection S n b
  exact (sigmaBarEquiv I σ ann hbij n).apply_symm_apply (projection S n b)

/-- Injectivity of the original quotient factors suffices for injectivity of the original map. -/
theorem completionMap_injective (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hinj : ∀ n : ℕ, Function.Injective (sigmaBar I σ ann n)) :
    Function.Injective (completionMap I σ ann S hσ) := by
  intro x y hxy
  apply Subtype.ext
  funext n
  cases n with
  | zero =>
    let := zeroQuotient_subsingleton (M := M) I
    exact Subsingleton.elim _ _
  | succ n =>
    apply hinj n
    exact congrArg (projection S n) hxy

/-- Bijective original quotient factors provide an actual preimage for every compatible family. -/
theorem completionMap_surjective (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) :
    Function.Surjective (completionMap I σ ann S hσ) :=
  fun b => ⟨completionPreimage I σ ann S hσ hbij b,
    completionMap_preimage I σ ann S hσ hbij b⟩

/-- Bijectivity applies to the unchanged original completion map, with no finite-generation premise. -/
theorem completionMap_bijective (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) :
    Function.Bijective (completionMap I σ ann S hσ) :=
  ⟨completionMap_injective I σ ann S hσ (fun n => (hbij n).1),
    completionMap_surjective I σ ann S hσ hbij⟩

/-- The linear equivalence whose forward map is the original completion map. -/
def completionEquiv (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) :
    AdicCompletion I M ≃ₗ[R] Sections S :=
  LinearEquiv.ofBijective (completionMap I σ ann S hσ)
    (completionMap_bijective I σ ann S hσ hbij)

/-- The forward linear map is definitionally the original completionMap. -/
theorem completionEquiv_toLinearMap (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) :
    (completionEquiv I σ ann S hσ hbij).toLinearMap = completionMap I σ ann S hσ := rfl

/-- Evaluation of the equivalence retains the existing completion-map action. -/
theorem completionEquiv_apply (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (x : AdicCompletion I M) :
    completionEquiv I σ ann S hσ hbij x = completionMap I σ ann S hσ x := rfl

/-- The inverse equivalence is the compatible coordinate preimage constructed above. -/
theorem completionEquiv_symm_apply (S : System R B)
    (hσ : ∀ {m n : ℕ} (hmn : m ≤ n), (S.transition hmn).comp (σ n) = σ m)
    (hbij : ∀ n : ℕ, Function.Bijective (sigmaBar I σ ann n)) (b : Sections S) :
    (completionEquiv I σ ann S hσ hbij).symm b = completionPreimage I σ ann S hσ hbij b := by
  apply (completionEquiv I σ ann S hσ hbij).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (completionMap_preimage I σ ann S hσ hbij b).symm

#print axioms zeroQuotient_subsingleton
#print axioms sigmaBarEquiv
#print axioms sigmaBarEquiv_toLinearMap
#print axioms inverseCoordinates
#print axioms inverseCoordinates_zero
#print axioms inverseCoordinates_succ
#print axioms inverseCoordinates_compatible
#print axioms completionPreimage
#print axioms completionMap_preimage
#print axioms completionMap_injective
#print axioms completionMap_surjective
#print axioms completionMap_bijective
#print axioms completionEquiv
#print axioms completionEquiv_toLinearMap
#print axioms completionEquiv_apply
#print axioms completionEquiv_symm_apply

end PrimeGap182.TypeIII.AdicCompatibleSystem
