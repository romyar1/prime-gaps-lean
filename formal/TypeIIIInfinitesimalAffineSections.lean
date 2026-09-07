import TypeIIIInfinitesimalCompletion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The original affine infinitesimal section quotients

For an affine scheme X over Spec R, the original restriction from Γ(X)
to Γ(X_n) is surjective and has kernel I^(n+1)Γ(X). The kernel is proved
using the actual pushout of global-section rings of the literal affine
pullback. Its universal property gives a map to the original quotient
of Γ(X), and hence detects exactly the elements killed by restriction.

Consequently the already constructed quotient factor sigmaBar is
bijective. The linear equivalence in this file has precisely that
original map as its forward linear map; no section map is substituted.

The base ring, ideal, and affine structure morphism are arbitrary. No
finite-generation, Noetherian, properness, nonemptiness, or completion
comparison hypothesis is imposed. This is the affine section quotient
statement and is not general proper formal functions.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.InfinitesimalAffineSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinitesimalSections
open scoped AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
  (I : Ideal R) (q : X ⟶ Spec (.of R))

/-- The original affine pullback gives the actual pushout of the four global-section rings. -/
theorem sectionSquare_isPushout (n : ℕ) :
    IsPushout q.appTop
      (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))).appTop
      (InfinitesimalIdempotentTower.inclusion I q n).appTop
      (pullback.snd q (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1)))).appTop :=
  isPushout_appTop_of_isPullback (IsPullback.of_hasPullback q
    (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))))

/-- The original inclusion map on global sections is surjective. -/
theorem restriction_surjective (n : ℕ) : Function.Surjective (restriction I q n) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine
    (InfinitesimalIdempotentTower.inclusion I q n)).2

/-- The actual ring-map kernel is exactly the image ideal under the original coefficient map. -/
theorem restriction_ker_ideal (n : ℕ) :
    RingHom.ker (InfinitesimalIdempotentTower.inclusion I q n).appTop.hom =
      (I ^ (n + 1)).map (ProperAffinization.coefficient q) := by
  let J : Ideal Γ(X, ⊤) := (I ^ (n + 1)).map (ProperAffinization.coefficient q)
  let π : Γ(X, ⊤) →+* Γ(X, ⊤) ⧸ J := Ideal.Quotient.mk J
  let a : R →+* Γ(X, ⊤) ⧸ J := π.comp (ProperAffinization.coefficient q)
  have ha : I ^ (n + 1) ≤ RingHom.ker a := by
    intro r hr
    change Ideal.Quotient.mk J (ProperAffinization.coefficient q r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  let b : R ⧸ I ^ (n + 1) →+* Γ(X, ⊤) ⧸ J :=
    Ideal.Quotient.lift (I ^ (n + 1)) a ha
  let c : Γ(Spec (.of (R ⧸ I ^ (n + 1))), ⊤) ⟶ .of (Γ(X, ⊤) ⧸ J) :=
    (Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).hom ≫ CommRingCat.ofHom b
  have hcomm : q.appTop ≫ CommRingCat.ofHom π =
      (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))).appTop ≫ c := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of R)).inv).mp
    dsimp only [c, NilpotentThickeningIdempotents.quotientSpec]
    simp only [← Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    ext r
    rfl
  let d := (sectionSquare_isPushout I q n).desc (CommRingCat.ofHom π) c hcomm
  have hd : (InfinitesimalIdempotentTower.inclusion I q n).appTop ≫ d =
      CommRingCat.ofHom π := (sectionSquare_isPushout I q n).inl_desc _ _ _
  refine le_antisymm ?_ ?_
  · intro s hs
    have hval := congrArg (fun f : Γ(X, ⊤) ⟶ .of (Γ(X, ⊤) ⧸ J) => f s) hd
    change d ((InfinitesimalIdempotentTower.inclusion I q n).appTop s) = π s at hval
    change (InfinitesimalIdempotentTower.inclusion I q n).appTop s = 0 at hs
    rw [hs, map_zero] at hval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hval.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change ProperAffinization.coefficient (InfinitesimalIdempotentTower.inclusion I q n ≫ q) r = 0
    exact levelCoefficient_eq_zero I q n hr

/-- In the original R-module structure, the same kernel is I^(n+1) times the whole source. -/
theorem restriction_ker (n : ℕ) :
    (restriction I q n).ker = I ^ (n + 1) • (⊤ : Submodule R (sourceModule q)) := by
  let := ProperAffinization.coefficientAlgebra q
  ext s
  change (InfinitesimalIdempotentTower.inclusion I q n).appTop.hom s = 0 ↔
    s ∈ I ^ (n + 1) • (⊤ : Submodule R Γ(X, ⊤))
  rw [Ideal.smul_top_eq_map]
  change s ∈ RingHom.ker (InfinitesimalIdempotentTower.inclusion I q n).appTop.hom ↔
    s ∈ (I ^ (n + 1)).map (ProperAffinization.coefficient q)
  rw [restriction_ker_ideal I q n]

/-- The original quotient factor from the completion construction is bijective in the affine case. -/
theorem sigmaBar_bijective (n : ℕ) :
    Function.Bijective
      (AdicCompatibleSystem.sigmaBar I (restriction I q) (levelModule_annihilated I q) n) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (restriction_ker I q n).le
  · intro t
    obtain ⟨s, hs⟩ := restriction_surjective I q n t
    refine ⟨(I ^ (n + 1) • (⊤ : Submodule R (sourceModule q))).mkQ s, ?_⟩
    exact hs

/-- The actual original sigmaBar, bundled as its now-proved linear equivalence. -/
def sigmaBarEquiv (n : ℕ) :
    ((sourceModule q : Type u) ⧸ (I ^ (n + 1) • (⊤ : Submodule R (sourceModule q)))) ≃ₗ[R]
      levelModule I q n :=
  LinearEquiv.ofBijective
    (AdicCompatibleSystem.sigmaBar I (restriction I q) (levelModule_annihilated I q) n)
    (sigmaBar_bijective I q n)

/-- The forward linear map is exactly the original completion-coordinate quotient factor. -/
theorem sigmaBarEquiv_toLinearMap (n : ℕ) :
    (sigmaBarEquiv I q n).toLinearMap =
      AdicCompatibleSystem.sigmaBar I (restriction I q) (levelModule_annihilated I q) n := rfl

/-- On representatives, the equivalence is the unchanged original inclusion's section map. -/
theorem sigmaBarEquiv_mkQ (n : ℕ) (s : sourceModule q) :
    sigmaBarEquiv I q n ((I ^ (n + 1) • (⊤ : Submodule R (sourceModule q))).mkQ s) =
      (InfinitesimalIdempotentTower.inclusion I q n).appTop s := rfl

#print axioms sectionSquare_isPushout
#print axioms restriction_surjective
#print axioms restriction_ker_ideal
#print axioms restriction_ker
#print axioms sigmaBar_bijective
#print axioms sigmaBarEquiv
#print axioms sigmaBarEquiv_toLinearMap
#print axioms sigmaBarEquiv_mkQ

end PrimeGap182.TypeIII.InfinitesimalAffineSections
