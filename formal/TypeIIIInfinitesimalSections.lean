import TypeIIIInfinitesimalIdempotentTower
import TypeIIIProperAffinization
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Original linear section maps on the infinitesimal tower

For an arbitrary ideal I of R and q : X → Spec R, the source module is
the original ring Γ(X, ⊤) with the coefficient algebra induced by q.
At level n the module is the original Γ(X_n, ⊤), where X_n is the literal
base change along Spec(R/I^(n+1)) → Spec R.  The linear restriction maps
are exactly the original inclusion and transition maps on global sections.

The coefficient map at level n factors through the original quotient map,
using the second projection of that same pullback.  Consequently I^(n+1)
annihilates the whole level module.  The original transition maps satisfy
their identity, composition, and restriction-compatibility equations.

No properness, Noetherianity, finite-generation, or nonemptiness hypothesis
is imposed.  This constructs linear maps and their actual module actions;
it does not supply formal functions or a lift from compatible sections to
Γ(X, ⊤).
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.InfinitesimalSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The original global-section module, with its named coefficient structure. -/
def sourceModule (q : X ⟶ Spec (.of R)) : ModuleCat.{u} R :=
  letI := ProperAffinization.coefficientAlgebra q
  ModuleCat.of R Γ(X, ⊤)

/-- The bundled source retains the original global-section carrier. -/
theorem sourceModule_carrier (q : X ⟶ Spec (.of R)) :
    (sourceModule q : Type u) = Γ(X, ⊤) := rfl

/-- Its scalar multiplication is multiplication by the original coefficient map. -/
theorem sourceModule_smul (q : X ⟶ Spec (.of R)) (r : R) (s : sourceModule q) :
    (show Γ(X, ⊤) from (r • s : sourceModule q)) =
      ProperAffinization.coefficient q r * (show Γ(X, ⊤) from s) := rfl

/-- Restriction of the original coefficient map along a scheme morphism. -/
theorem coefficient_comp {Y : Scheme.{u}} (q : X ⟶ Spec (.of R)) (f : Y ⟶ X) :
    ProperAffinization.coefficient (f ≫ q) =
      f.appTop.hom.comp (ProperAffinization.coefficient q) := rfl

/-- Normalization of coefficients commutes with an actual affine base map. -/
theorem coefficient_comp_specMap {S : Type u} [CommRing S]
    (q : X ⟶ Spec (.of S)) (f : R →+* S) :
    ProperAffinization.coefficient (q ≫ Spec.map (CommRingCat.ofHom f)) =
      (ProperAffinization.coefficient q).comp f := by
  unfold ProperAffinization.coefficient
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The original map on sections of a morphism over the same affine base is R-linear. -/
def sectionMap {Y : Scheme.{u}} (q : X ⟶ Spec (.of R)) (p : Y ⟶ Spec (.of R))
    (f : Y ⟶ X) (hf : f ≫ q = p) : sourceModule q →ₗ[R] sourceModule p where
  toFun := f.appTop
  map_add' s t := f.appTop.hom.map_add _ _
  map_smul' r s := by
    change f.appTop.hom (ProperAffinization.coefficient q r * (show Γ(X, ⊤) from s)) =
      ProperAffinization.coefficient p r * f.appTop.hom (show Γ(X, ⊤) from s)
    rw [map_mul]
    have hcoeff : f.appTop (ProperAffinization.coefficient q r) =
        ProperAffinization.coefficient p r := by
      rw [← hf]
      rfl
    rw [hcoeff]

/-- The linear map has exactly the original map on global sections as its underlying function. -/
theorem sectionMap_apply {Y : Scheme.{u}} (q : X ⟶ Spec (.of R))
    (p : Y ⟶ Spec (.of R)) (f : Y ⟶ X) (hf : f ≫ q = p) (s : sourceModule q) :
    sectionMap q p f hf s = f.appTop s := rfl

variable (I : Ideal R) (q : X ⟶ Spec (.of R))

/-- The actual level-n section module with coefficients from its original map to Spec R. -/
def levelModule (n : ℕ) : ModuleCat.{u} R :=
  sourceModule (InfinitesimalIdempotentTower.inclusion I q n ≫ q)

/-- The level module has the original infinitesimal global-section ring as its carrier. -/
theorem levelModule_carrier (n : ℕ) :
    (levelModule I q n : Type u) = Γ(InfinitesimalIdempotentTower.thickening I q n, ⊤) := rfl

/-- Level scalars act through the original coefficient map of the original thickening. -/
theorem levelModule_smul (n : ℕ) (r : R) (s : levelModule I q n) :
    (show Γ(InfinitesimalIdempotentTower.thickening I q n, ⊤) from
      (r • s : levelModule I q n)) =
      ProperAffinization.coefficient (InfinitesimalIdempotentTower.inclusion I q n ≫ q) r *
        (show Γ(InfinitesimalIdempotentTower.thickening I q n, ⊤) from s) := rfl

/-- The original inclusion induces this actual R-linear restriction map. -/
def restriction (n : ℕ) : sourceModule q →ₗ[R] levelModule I q n :=
  sectionMap q (InfinitesimalIdempotentTower.inclusion I q n ≫ q)
    (InfinitesimalIdempotentTower.inclusion I q n) rfl

/-- Restriction is exactly the original inclusion's map on global sections. -/
theorem restriction_apply (n : ℕ) (s : sourceModule q) :
    restriction I q n s = (InfinitesimalIdempotentTower.inclusion I q n).appTop s := rfl

/-- The original quotient-induced transition gives the actual R-linear map from level n to m. -/
def transition {m n : ℕ} (hmn : m ≤ n) : levelModule I q n →ₗ[R] levelModule I q m :=
  sectionMap (InfinitesimalIdempotentTower.inclusion I q n ≫ q)
    (InfinitesimalIdempotentTower.inclusion I q m ≫ q)
    (InfinitesimalIdempotentTower.transition I q hmn) (by
      rw [← Category.assoc, InfinitesimalIdempotentTower.transition_comp_inclusion])

/-- The transition is the original scheme transition's map on global sections. -/
theorem transition_apply {m n : ℕ} (hmn : m ≤ n) (s : levelModule I q n) :
    transition I q hmn s = (InfinitesimalIdempotentTower.transition I q hmn).appTop s := rfl

/-- The original section transition at an equal index is the identity linear map. -/
theorem transition_refl (n : ℕ) : transition I q (le_refl n) = LinearMap.id := by
  ext s
  change (InfinitesimalIdempotentTower.transition I q (le_refl n)).appTop s = s
  rw [InfinitesimalIdempotentTower.transition_refl]
  rfl

/-- The actual linear transitions compose in the original contravariant direction. -/
theorem transition_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (transition I q hkm).comp (transition I q hmn) = transition I q (hkm.trans hmn) := by
  ext s
  change (InfinitesimalIdempotentTower.transition I q hkm ≫
    InfinitesimalIdempotentTower.transition I q hmn).appTop s =
      (InfinitesimalIdempotentTower.transition I q (hkm.trans hmn)).appTop s
  rw [InfinitesimalIdempotentTower.transition_comp]

/-- All original source restrictions are compatible with the original transition maps. -/
theorem transition_comp_restriction {m n : ℕ} (hmn : m ≤ n) :
    (transition I q hmn).comp (restriction I q n) = restriction I q m := by
  ext s
  change (InfinitesimalIdempotentTower.transition I q hmn ≫
    InfinitesimalIdempotentTower.inclusion I q n).appTop s =
      (InfinitesimalIdempotentTower.inclusion I q m).appTop s
  rw [InfinitesimalIdempotentTower.transition_comp_inclusion]

/-- The coefficient map from the literal quotient ring, induced by the second pullback projection. -/
def quotientCoefficient (n : ℕ) :
    R ⧸ I ^ (n + 1) →+* Γ(InfinitesimalIdempotentTower.thickening I q n, ⊤) :=
  ProperAffinization.coefficient
    (pullback.snd q (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))))

/-- The second projection gives the exact factorization of the original R-coefficient map. -/
theorem quotientCoefficient_factor (n : ℕ) :
    (quotientCoefficient I q n).comp (Ideal.Quotient.mk (I ^ (n + 1))) =
      ProperAffinization.coefficient (InfinitesimalIdempotentTower.inclusion I q n ≫ q) := by
  unfold quotientCoefficient
  rw [← coefficient_comp_specMap]
  change ProperAffinization.coefficient
      (pullback.snd q (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))) ≫
        NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))) =
    ProperAffinization.coefficient
      (pullback.fst q (NilpotentThickeningIdempotents.quotientSpec (I ^ (n + 1))) ≫ q)
  exact congrArg ProperAffinization.coefficient pullback.condition.symm

/-- Pointwise form of the factorization through the original quotient map. -/
theorem quotientCoefficient_factor_apply (n : ℕ) (r : R) :
    quotientCoefficient I q n (Ideal.Quotient.mk (I ^ (n + 1)) r) =
      ProperAffinization.coefficient (InfinitesimalIdempotentTower.inclusion I q n ≫ q) r :=
  congrArg (fun f : R →+* Γ(InfinitesimalIdempotentTower.thickening I q n, ⊤) => f r)
    (quotientCoefficient_factor I q n)

/-- Every coefficient in the indicated ideal power acts by the zero section. -/
theorem levelCoefficient_eq_zero (n : ℕ) {r : R} (hr : r ∈ I ^ (n + 1)) :
    ProperAffinization.coefficient (InfinitesimalIdempotentTower.inclusion I q n ≫ q) r = 0 := by
  rw [← quotientCoefficient_factor_apply I q n r,
    Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- The actual module action is annihilated elementwise by I^(n+1). -/
theorem levelModule_smul_eq_zero (n : ℕ) {r : R} (hr : r ∈ I ^ (n + 1))
    (s : levelModule I q n) : r • s = 0 := by
  change ProperAffinization.coefficient (InfinitesimalIdempotentTower.inclusion I q n ≫ q) r *
    (show Γ(InfinitesimalIdempotentTower.thickening I q n, ⊤) from s) = 0
  rw [levelCoefficient_eq_zero I q n hr, zero_mul]

/-- The full actual section module is annihilated by the original ideal power. -/
theorem levelModule_annihilated (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (levelModule I q n)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine Submodule.smul_le.mpr ?_
  intro r hr s _hs
  exact (Submodule.mem_bot R).mpr (levelModule_smul_eq_zero I q n hr s)

end PrimeGap182.TypeIII.InfinitesimalSections

#print axioms PrimeGap182.TypeIII.InfinitesimalSections.sourceModule
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.sourceModule_carrier
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.sourceModule_smul
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.coefficient_comp
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.coefficient_comp_specMap
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.sectionMap
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.sectionMap_apply
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelModule
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelModule_carrier
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelModule_smul
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.restriction
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.restriction_apply
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.transition
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.transition_apply
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.transition_refl
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.transition_comp
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.transition_comp_restriction
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.quotientCoefficient
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.quotientCoefficient_factor
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.quotientCoefficient_factor_apply
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelCoefficient_eq_zero
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelModule_smul_eq_zero
#print axioms PrimeGap182.TypeIII.InfinitesimalSections.levelModule_annihilated
