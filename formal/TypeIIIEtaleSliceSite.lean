import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# The actual slice of the small étale site

For an étale S-scheme Y, objects of the slice of S.Etale over Y are
exactly schemes étale over Y. The equivalence retains the underlying
scheme maps. Consequently the covering topologies agree: both are
defined by joint surjectivity of those maps.

Transport along this proved equivalence supplies sheafification on the
slice in the same coefficient universe as the original small étale site.
-/

noncomputable section

universe u v w

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) (Y : S.Etale)

set_option backward.isDefEq.respectTransparency.types false in
/-- An object over Y in the small étale site gives its actual structure
morphism as a scheme étale over Y.left. -/
def etaleSliceToEtale : Over Y ⥤ Y.left.Etale where
  obj Z := Scheme.Etale.mk Z.hom.left
  map {Z W} g := MorphismProperty.Over.homMk g.left.left (by
    exact (Scheme.Etale.forget S ⋙ Over.forget S).congr_map (Over.w g))
  map_id Z := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  map_comp g h := by
    apply MorphismProperty.Over.Hom.ext
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Composition with Y → S regards each scheme étale over Y as an
object of the actual slice of S.Etale. -/
def etaleToSlice : Y.left.Etale ⥤ Over Y where
  obj Z := Over.mk (MorphismProperty.Over.homMk Z.hom :
    Scheme.Etale.mk (Z.hom ≫ Y.hom) ⟶ Y)
  map {Z W} g := Over.homMk
    (MorphismProperty.Over.homMk g.left (by
      change g.left ≫ (W.hom ≫ Y.hom) = Z.hom ≫ Y.hom
      rw [← Category.assoc, MorphismProperty.Over.w g]))
    (by
      apply MorphismProperty.Over.Hom.ext
      exact MorphismProperty.Over.w g)
  map_id Z := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl
  map_comp g h := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Forgetting and restoring the outer base leaves the original slice
object canonically isomorphic through the identity scheme map. -/
def etaleSliceUnitIso : 𝟭 (Over Y) ≅ etaleSliceToEtale S Y ⋙ etaleToSlice S Y :=
  NatIso.ofComponents (fun Z =>
    Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl Z.left.left)
      (by
        change (𝟙 Z.left.left) ≫ (Z.hom.left ≫ Y.hom) = Z.left.hom
        rw [Category.id_comp]
        exact MorphismProperty.Over.w Z.hom)))
    (by
      intro Z W g
      apply Over.OverMorphism.ext
      apply MorphismProperty.Over.Hom.ext
      change g.left.left ≫ 𝟙 W.left.left = (𝟙 Z.left.left) ≫ g.left.left
      simp only [Category.comp_id, Category.id_comp])

set_option backward.isDefEq.respectTransparency.types false in
/-- Restoring and forgetting the outer base leaves the same étale
Y-scheme, with identity underlying comparison. -/
def etaleSliceCounitIso : etaleToSlice S Y ⋙ etaleSliceToEtale S Y ≅ 𝟭 Y.left.Etale :=
  NatIso.ofComponents (fun Z => MorphismProperty.Over.isoMk (Iso.refl Z.left))
    (by
      intro Z W g
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 W.left = (𝟙 Z.left) ≫ g.left
      simp only [Category.comp_id, Category.id_comp])

/-- The literal slice category of the small étale site is equivalent
to the small étale category of the covering scheme. -/
def etaleSliceEquiv : Over Y ≌ Y.left.Etale :=
  CategoryTheory.Equivalence.mk (etaleSliceToEtale S Y) (etaleToSlice S Y)
    (etaleSliceUnitIso S Y) (etaleSliceCounitIso S Y)

instance etaleSliceToEtale_isEquivalence : (etaleSliceToEtale S Y).IsEquivalence :=
  (etaleSliceEquiv S Y).isEquivalence_functor

instance etaleToSlice_isEquivalence : (etaleToSlice S Y).IsEquivalence :=
  (etaleSliceEquiv S Y).isEquivalence_inverse

/-- The forward equivalence leaves every underlying scheme map unchanged. -/
@[simp] theorem etaleSliceToEtale_map_left {Z W : Over Y} (g : Z ⟶ W) :
    ((etaleSliceToEtale S Y).map g).left = g.left.left := rfl

/-- The inverse equivalence also leaves every underlying scheme map unchanged. -/
@[simp] theorem etaleToSlice_map_left_left {Z W : Y.left.Etale} (g : Z ⟶ W) :
    ((etaleToSlice S Y).map g).left.left = g.left := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- A sieve covers in the actual slice topology exactly when its image
covers the same scheme in the small étale topology of Y. -/
theorem etaleSliceToEtale_cover_iff {Z : Over Y} (T : Sieve Z) :
    T.functorPushforward (etaleSliceToEtale S Y) ∈
        Y.left.smallEtaleTopology ((etaleSliceToEtale S Y).obj Z) ↔
      T ∈ (S.smallEtaleTopology.over Y) Z := by
  obtain ⟨ι, W, g, rfl⟩ := T.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff,
    Scheme.ofArrows_mem_smallEtaleTopology_iff]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse equivalence preserves and reflects the actual covers. -/
theorem etaleToSlice_cover_iff {Z : Y.left.Etale} (T : Sieve Z) :
    T.functorPushforward (etaleToSlice S Y) ∈
        (S.smallEtaleTopology.over Y) ((etaleToSlice S Y).obj Z) ↔
      T ∈ Y.left.smallEtaleTopology Z := by
  obtain ⟨ι, W, g, rfl⟩ := T.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff,
    Scheme.ofArrows_mem_smallEtaleTopology_iff]
  rfl

instance etaleSliceToEtale_isDenseSubsite :
    (etaleSliceToEtale S Y).IsDenseSubsite
      (S.smallEtaleTopology.over Y) Y.left.smallEtaleTopology where
  functorPushforward_mem_iff := etaleSliceToEtale_cover_iff S Y _

instance etaleToSlice_isDenseSubsite :
    (etaleToSlice S Y).IsDenseSubsite
      Y.left.smallEtaleTopology (S.smallEtaleTopology.over Y) where
  functorPushforward_mem_iff := etaleToSlice_cover_iff S Y _

/-- Sheafification on the actual small étale site of Y transports to
the actual slice topology, without enlarging the coefficient category. -/
instance etaleSlice_hasSheafify (A : Type v) [Category.{w} A]
    [HasSheafify Y.left.smallEtaleTopology A] :
    HasSheafify (S.smallEtaleTopology.over Y) A := by
  let : (etaleSliceEquiv S Y).inverse.IsDenseSubsite
      Y.left.smallEtaleTopology (S.smallEtaleTopology.over Y) :=
    etaleToSlice_isDenseSubsite S Y
  exact (etaleSliceEquiv S Y).hasSheafify
    (S.smallEtaleTopology.over Y) Y.left.smallEtaleTopology A

/-- In particular, the actual slice admits sheafification for sets in
the same universe as the schemes. -/
theorem etaleSlice_types_hasSheafify :
    HasSheafify (S.smallEtaleTopology.over Y) (Type u) := inferInstance

/-- The actual slice admits sheafification of modules in the original
coefficient universe; this applies to the character sheaf coefficients. -/
theorem etaleSlice_modules_hasSheafify (E : Type u) [Ring E] :
    HasSheafify (S.smallEtaleTopology.over Y) (ModuleCat.{u} E) := inferInstance

/-- Restriction along the inverse slice equivalence is the actual
equivalence of sheaf categories supplied by the equivalent sites. -/
instance etaleToSlice_sheafPushforward_isEquivalence (A : Type v) [Category.{w} A] :
    ((etaleToSlice S Y).sheafPushforwardContinuous A
      Y.left.smallEtaleTopology (S.smallEtaleTopology.over Y)).IsEquivalence := by
  let : (etaleSliceEquiv S Y).inverse.IsDenseSubsite
      Y.left.smallEtaleTopology (S.smallEtaleTopology.over Y) :=
    etaleToSlice_isDenseSubsite S Y
  exact ((etaleSliceEquiv S Y).sheafCongr
    (S.smallEtaleTopology.over Y) Y.left.smallEtaleTopology A).isEquivalence_functor

/-- On the actual slice site, maps of set-valued presheaves inverted
by sheafification are precisely the locally bijective maps. -/
instance etaleSlice_types_WEqualsLocallyBijective :
    (S.smallEtaleTopology.over Y).WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.transport
    (S.smallEtaleTopology.over Y) Y.left.smallEtaleTopology (etaleToSlice S Y)
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- The same local criterion holds for modules in the original
coefficient universe. -/
instance etaleSlice_modules_WEqualsLocallyBijective (E : Type u) [Ring E] :
    (S.smallEtaleTopology.over Y).WEqualsLocallyBijective (ModuleCat.{u} E) :=
  GrothendieckTopology.WEqualsLocallyBijective.transport
    (S.smallEtaleTopology.over Y) Y.left.smallEtaleTopology (etaleToSlice S Y)
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- Forgetting the module structure preserves sheaves on the actual
slice site, so module sheaves have their usual underlying set sheaves. -/
theorem etaleSlice_modules_hasSheafCompose_forget (E : Type u) [Ring E] :
    (S.smallEtaleTopology.over Y).HasSheafCompose (forget (ModuleCat.{u} E)) :=
  inferInstance

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.etaleSliceToEtale
#print axioms PrimeGap182.TypeIII.etaleToSlice
#print axioms PrimeGap182.TypeIII.etaleSliceUnitIso
#print axioms PrimeGap182.TypeIII.etaleSliceCounitIso
#print axioms PrimeGap182.TypeIII.etaleSliceEquiv
#print axioms PrimeGap182.TypeIII.etaleSliceToEtale_isEquivalence
#print axioms PrimeGap182.TypeIII.etaleToSlice_isEquivalence
#print axioms PrimeGap182.TypeIII.etaleSliceToEtale_map_left
#print axioms PrimeGap182.TypeIII.etaleToSlice_map_left_left
#print axioms PrimeGap182.TypeIII.etaleSliceToEtale_cover_iff
#print axioms PrimeGap182.TypeIII.etaleToSlice_cover_iff
#print axioms PrimeGap182.TypeIII.etaleSliceToEtale_isDenseSubsite
#print axioms PrimeGap182.TypeIII.etaleToSlice_isDenseSubsite
#print axioms PrimeGap182.TypeIII.etaleSlice_hasSheafify
#print axioms PrimeGap182.TypeIII.etaleSlice_types_hasSheafify
#print axioms PrimeGap182.TypeIII.etaleSlice_modules_hasSheafify
#print axioms PrimeGap182.TypeIII.etaleToSlice_sheafPushforward_isEquivalence
#print axioms PrimeGap182.TypeIII.etaleSlice_types_WEqualsLocallyBijective
#print axioms PrimeGap182.TypeIII.etaleSlice_modules_WEqualsLocallyBijective
#print axioms PrimeGap182.TypeIII.etaleSlice_modules_hasSheafCompose_forget
