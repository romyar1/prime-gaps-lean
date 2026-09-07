import TypeIIIInfinitesimalSections
import TypeIIIAdicCompatibleSystem

/-!
# The canonical completion comparison for the actual infinitesimal schemes

The source is the completion of the original global-section module.
The target consists of compatible sections of the literal infinitesimal
schemes X_n, with their original quotient-induced restriction maps.
The comparison is constructed coordinate by coordinate from the original
completion evaluation and the original map on global sections. Its
normalization on original sections is proved, not supplied as a premise.

Every closed-fiber idempotent supplies an actual compatible target family.
If that family has a preimage under this comparison and the ideal is
finitely generated, range descent gives a section of the original scheme
with the prescribed closed-fiber value. Surjectivity of the comparison
is not assumed in its construction and remains unproved here. In
particular this is not a formal-functions or proper-base-change theorem.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.InfinitesimalCompletion

open AlgebraicGeometry CategoryTheory
open InfinitesimalSections
open scoped AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (I : Ideal R) (q : X ⟶ Spec (.of R))

/-- The system consists of the original section modules and original transitions. -/
def system : AdicCompatibleSystem.System R (fun n => (levelModule I q n : Type u)) where
  transition := fun hmn => InfinitesimalSections.transition I q hmn
  transition_refl := transition_refl I q
  transition_comp := fun hkm hmn => transition_comp I q hkm hmn

/-- Literal compatible families of global sections on the original infinitesimal schemes. -/
abbrev Sections : Type u := AdicCompatibleSystem.Sections (system I q)

/-- Evaluation at the original n-th infinitesimal scheme. -/
def projection (n : ℕ) : Sections I q →ₗ[R] levelModule I q n :=
  AdicCompatibleSystem.projection (system I q) n

/-- The compatible family of restrictions of an original global section. -/
def originalRestriction : sourceModule q →ₗ[R] Sections I q :=
  AdicCompatibleSystem.originalMap (system I q) (restriction I q)
    (fun hmn => transition_comp_restriction I q hmn)

/-- The original n-th section map extended through its quotient factor and completion evaluation. -/
def completedRestriction (n : ℕ) :
    AdicCompletion I (sourceModule q) →ₗ[R] levelModule I q n :=
  AdicCompatibleSystem.completionCoordinate I (restriction I q)
    (levelModule_annihilated I q) n

/-- The actual canonical map from the completion to compatible infinitesimal sections. -/
def completionMap : AdicCompletion I (sourceModule q) →ₗ[R] Sections I q :=
  AdicCompatibleSystem.completionMap I (restriction I q)
    (levelModule_annihilated I q) (system I q)
    (fun hmn => transition_comp_restriction I q hmn)

/-- Every coordinate of the constructed comparison is the original completed restriction. -/
theorem projection_completionMap (n : ℕ) :
    (projection I q n).comp (completionMap I q) = completedRestriction I q n := rfl

/-- The coordinate formula uses the original evaluation at n+1 and the original quotient factor. -/
theorem completionMap_eval (x : AdicCompletion I (sourceModule q)) (n : ℕ) :
    projection I q n (completionMap I q x) =
      AdicCompatibleSystem.sigmaBar I (restriction I q) (levelModule_annihilated I q) n
        (AdicCompletion.eval I (sourceModule q) (n + 1) x) := rfl

/-- On original sections, the completed restriction is the original inclusion's appTop. -/
theorem completedRestriction_of (n : ℕ) (a : sourceModule q) :
    completedRestriction I q n (AdicCompletion.of I (sourceModule q) a) =
      (InfinitesimalIdempotentTower.inclusion I q n).appTop a := rfl

/-- The whole comparison agrees with the original compatible restriction family. -/
theorem completionMap_comp_of :
    (completionMap I q).comp (AdicCompletion.of I (sourceModule q)) =
      originalRestriction I q :=
  AdicCompatibleSystem.completionMap_comp_of I (restriction I q)
    (levelModule_annihilated I q) (system I q)
    (fun hmn => transition_comp_restriction I q hmn)

/-- Completed restrictions commute with the original transitions of the actual schemes. -/
theorem completedRestriction_transition {m n : ℕ} (hmn : m ≤ n) :
    (InfinitesimalSections.transition I q hmn).comp (completedRestriction I q n) =
      completedRestriction I q m :=
  AdicCompatibleSystem.completionCoordinate_transition I (restriction I q)
    (levelModule_annihilated I q) (system I q)
    (fun h => transition_comp_restriction I q h) hmn

/-- For a finitely generated ideal, the comparison is the unique linear extension
of the original compatible family of restrictions. -/
theorem completionMap_unique (hI : I.FG)
    (L : AdicCompletion I (sourceModule q) →ₗ[R] Sections I q)
    (hL : L.comp (AdicCompletion.of I (sourceModule q)) = originalRestriction I q) :
    L = completionMap I q :=
  AdicCompatibleSystem.completionMap_unique I (restriction I q)
    (levelModule_annihilated I q) (system I q)
    (fun hmn => transition_comp_restriction I q hmn) hI L hL

/-- At each fixed infinitesimal level the completed map has exactly the range
of the original restriction. This asserts no surjectivity onto compatible families. -/
theorem completedRestriction_range_eq (hI : I.FG) (n : ℕ) :
    LinearMap.range (completedRestriction I q n) = LinearMap.range (restriction I q n) := by
  have h := adicCompletion_range_comp_of_eq I (n + 1) (completedRestriction I q n)
    hI (levelModule_annihilated I q n)
  have hof : (completedRestriction I q n).comp (AdicCompletion.of I (sourceModule q)) =
      restriction I q n := by
    ext a
    rfl
  rw [hof] at h
  exact h.symm

/-- The previously constructed unique idempotent lifts give a literal compatible section family. -/
def idempotentFamily
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) : Sections I q :=
  ⟨fun n => (InfinitesimalIdempotentTower.lift I q e n).val,
    fun hmn => InfinitesimalIdempotentTower.lift_compatible_appTop I q e hmn⟩

/-- The family's coordinate is the original uniquely lifted idempotent. -/
theorem idempotentFamily_projection
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) (n : ℕ) :
    projection I q n (idempotentFamily I q e) =
      (InfinitesimalIdempotentTower.lift I q e n).val := rfl

/-- The zeroth coordinate is the originally specified idempotent. -/
theorem idempotentFamily_zero
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) :
    projection I q 0 (idempotentFamily I q e) = e.val :=
  congrArg Subtype.val (InfinitesimalIdempotentTower.lift_zero I q e)

/-- A completed preimage of the actual compatible idempotent family gives an
original section with the prescribed zeroth-level value. The existence of that
completed preimage is explicit and is not proved by this implication. -/
theorem exists_original_section_of_completed_idempotent_lift (hI : I.FG)
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0))
    (x : AdicCompletion I (sourceModule q))
    (hx : completionMap I q x = idempotentFamily I q e) :
    ∃ a : sourceModule q, (InfinitesimalIdempotentTower.inclusion I q 0).appTop a = e.val := by
  obtain ⟨a, ha⟩ := adicCompletion_exists_original_preimage I 1
    (completedRestriction I q 0) hI (levelModule_annihilated I q 0) x
  refine ⟨a, ?_⟩
  change completedRestriction I q 0 (AdicCompletion.of I (sourceModule q) a) = e.val
  rw [ha]
  change projection I q 0 (completionMap I q x) = e.val
  rw [hx, idempotentFamily_zero]

#print axioms system
#print axioms Sections
#print axioms projection
#print axioms originalRestriction
#print axioms completedRestriction
#print axioms completionMap
#print axioms projection_completionMap
#print axioms completionMap_eval
#print axioms completedRestriction_of
#print axioms completionMap_comp_of
#print axioms completedRestriction_transition
#print axioms completionMap_unique
#print axioms completedRestriction_range_eq
#print axioms idempotentFamily
#print axioms idempotentFamily_projection
#print axioms idempotentFamily_zero
#print axioms exists_original_section_of_completed_idempotent_lift

end PrimeGap182.TypeIII.InfinitesimalCompletion
