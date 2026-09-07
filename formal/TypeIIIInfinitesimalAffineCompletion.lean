import TypeIIIInfinitesimalAffineSections
import TypeIIIAdicCompatibleSystemEquivalence

/-!
# The original infinitesimal completion comparison for an affine scheme

For an affine scheme X over Spec R, the existing canonical completion
map to compatible sections of the literal infinitesimal schemes is
bijective. Its linear equivalence retains that exact forward map, and
the inverse coordinates use the original affine quotient factors.

The previously constructed compatible idempotent family therefore has
an actual completed preimage. Surjectivity of the original affine
restriction also supplies an original global section with any specified
finite-level value. No idempotence of that original section is asserted.

Only affineness is needed beyond the original ring, ideal, and morphism.
There are no finite-generation, Noetherian, properness, or nonemptiness
hypotheses. This is the affine comparison, not general proper formal
functions.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.InfinitesimalAffineCompletion

open AlgebraicGeometry CategoryTheory
open InfinitesimalSections
open scoped AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
  (I : Ideal R) (q : X ⟶ Spec (.of R))

/-- The unchanged canonical completion map is bijective in the actual affine case. -/
theorem completionMap_bijective :
    Function.Bijective (InfinitesimalCompletion.completionMap I q) :=
  AdicCompatibleSystem.completionMap_bijective I (restriction I q)
    (levelModule_annihilated I q) (InfinitesimalCompletion.system I q)
    (fun hmn => transition_comp_restriction I q hmn)
    (InfinitesimalAffineSections.sigmaBar_bijective I q)

/-- The actual canonical comparison, bundled as its proved linear equivalence. -/
def completionEquiv :
    AdicCompletion I (sourceModule q) ≃ₗ[R] InfinitesimalCompletion.Sections I q :=
  LinearEquiv.ofBijective (InfinitesimalCompletion.completionMap I q)
    (completionMap_bijective I q)

/-- The forward linear map is definitionally the original canonical comparison. -/
theorem completionEquiv_toLinearMap :
    (completionEquiv I q).toLinearMap = InfinitesimalCompletion.completionMap I q := rfl

/-- Applying the equivalence applies the unchanged canonical comparison. -/
theorem completionEquiv_apply (x : AdicCompletion I (sourceModule q)) :
    completionEquiv I q x = InfinitesimalCompletion.completionMap I q x := rfl

/-- On original sections the equivalence gives the original compatible restriction family. -/
theorem completionEquiv_of (a : sourceModule q) :
    completionEquiv I q (AdicCompletion.of I (sourceModule q) a) =
      InfinitesimalCompletion.originalRestriction I q a :=
  LinearMap.congr_fun (InfinitesimalCompletion.completionMap_comp_of I q) a

/-- The forward coordinates retain the original completion evaluation and affine quotient map. -/
theorem completionEquiv_eval (x : AdicCompletion I (sourceModule q)) (n : ℕ) :
    InfinitesimalCompletion.projection I q n (completionEquiv I q x) =
      InfinitesimalAffineSections.sigmaBarEquiv I q n
        (AdicCompletion.eval I (sourceModule q) (n + 1) x) := rfl

/-- Every positive inverse coordinate is the inverse of the original affine sigmaBar. -/
theorem completionEquiv_symm_eval (b : InfinitesimalCompletion.Sections I q) (n : ℕ) :
    AdicCompletion.eval I (sourceModule q) (n + 1) ((completionEquiv I q).symm b) =
      (InfinitesimalAffineSections.sigmaBarEquiv I q n).symm
        (InfinitesimalCompletion.projection I q n b) := by
  apply (InfinitesimalAffineSections.sigmaBarEquiv I q n).injective
  rw [LinearEquiv.apply_symm_apply]
  have h : InfinitesimalCompletion.completionMap I q ((completionEquiv I q).symm b) = b :=
    (completionEquiv I q).apply_symm_apply b
  exact congrArg (InfinitesimalCompletion.projection I q n) h

/-- The completed preimage of the existing compatible family of actual idempotent lifts. -/
def completedIdempotentLift
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) :
    AdicCompletion I (sourceModule q) :=
  (completionEquiv I q).symm (InfinitesimalCompletion.idempotentFamily I q e)

/-- The original completion map sends this preimage to the original idempotent family. -/
theorem completionMap_completedIdempotentLift
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) :
    InfinitesimalCompletion.completionMap I q (completedIdempotentLift I q e) =
      InfinitesimalCompletion.idempotentFamily I q e :=
  (completionEquiv I q).apply_symm_apply (InfinitesimalCompletion.idempotentFamily I q e)

/-- At each original infinitesimal level, the completed restriction is the previously proved lift. -/
theorem completedIdempotentLift_restriction
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) (n : ℕ) :
    InfinitesimalCompletion.completedRestriction I q n (completedIdempotentLift I q e) =
      (InfinitesimalIdempotentTower.lift I q e n).val := by
  change InfinitesimalCompletion.projection I q n
    (InfinitesimalCompletion.completionMap I q (completedIdempotentLift I q e)) = _
  rw [completionMap_completedIdempotentLift, InfinitesimalCompletion.idempotentFamily_projection]

/-- The original zeroth completed restriction is the prescribed closed-fiber idempotent value. -/
theorem completedIdempotentLift_zero
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) :
    InfinitesimalCompletion.completedRestriction I q 0 (completedIdempotentLift I q e) = e.val := by
  change InfinitesimalCompletion.projection I q 0
    (InfinitesimalCompletion.completionMap I q (completedIdempotentLift I q e)) = _
  rw [completionMap_completedIdempotentLift, InfinitesimalCompletion.idempotentFamily_zero]

/-- The actual compatible idempotent family has a completed preimage, without an FG premise. -/
theorem exists_completed_idempotent_lift
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) :
    ∃ x : AdicCompletion I (sourceModule q),
      InfinitesimalCompletion.completionMap I q x =
        InfinitesimalCompletion.idempotentFamily I q e :=
  ⟨completedIdempotentLift I q e, completionMap_completedIdempotentLift I q e⟩

/-- Direct affine restriction gives an original global section with any prescribed finite-level value. -/
theorem exists_original_section (n : ℕ) (t : levelModule I q n) :
    ∃ a : Γ(X, ⊤), (InfinitesimalIdempotentTower.inclusion I q n).appTop a = t :=
  InfinitesimalAffineSections.restriction_surjective I q n t

/-- In particular a prescribed closed-fiber idempotent value is attained by an original section.
The preimage is asserted to be a section, without an idempotence claim. -/
theorem exists_original_closed_fiber_idempotent_value
    (e : NilpotentThickeningIdempotents.GlobalIdempotents
      (InfinitesimalIdempotentTower.thickening I q 0)) :
    ∃ a : Γ(X, ⊤), (InfinitesimalIdempotentTower.inclusion I q 0).appTop a = e.val :=
  exists_original_section I q 0 e.val

#print axioms completionMap_bijective
#print axioms completionEquiv
#print axioms completionEquiv_toLinearMap
#print axioms completionEquiv_apply
#print axioms completionEquiv_of
#print axioms completionEquiv_eval
#print axioms completionEquiv_symm_eval
#print axioms completedIdempotentLift
#print axioms completionMap_completedIdempotentLift
#print axioms completedIdempotentLift_restriction
#print axioms completedIdempotentLift_zero
#print axioms exists_completed_idempotent_lift
#print axioms exists_original_section
#print axioms exists_original_closed_fiber_idempotent_value

end PrimeGap182.TypeIII.InfinitesimalAffineCompletion
