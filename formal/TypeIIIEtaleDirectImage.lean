import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual direct image on the small étale site

For an arbitrary morphism q : X → S, base change sends S-étale schemes
to X-étale schemes. It preserves finite limits and jointly surjective
étale covers, so precomposition gives the actual direct-image functor
on module sheaves. Its value on U is the original sheaf evaluated on
U ×[S] X. The resulting functor is additive and left exact.

No étaleness or properness of q, supplied continuity, or supplied
geometric functor is assumed. The target remains sheaves on S.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDirectImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

variable {X S : Scheme.{u}} (q : X ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual base change on the objects and morphisms of the small étale category. -/
def baseChange : S.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale) ⊤ q

/-- The underlying scheme is the categorical scheme fiber product. -/
theorem baseChange_obj_left (U : S.Etale) :
    ((baseChange q).obj U).left = pullback U.hom q := rfl

/-- The étale structure morphism is the second projection of the fiber product. -/
theorem baseChange_obj_hom (U : S.Etale) :
    ((baseChange q).obj U).hom = pullback.snd U.hom q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Base change of an arrow is the actual map of scheme fiber products. -/
theorem baseChange_map_left {U V : S.Etale} (f : U ⟶ V) :
    ((baseChange q).map f).left =
      pullback.map U.hom q V.hom q f.left (𝟙 X) (𝟙 S)
        (by simp) (by simp) := by
  change pullback.lift _ _ _ = pullback.lift _ _ _
  simp only [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The range of a base-changed arrow is the inverse image of its original range. -/
theorem baseChange_map_range {U V : S.Etale} (f : U ⟶ V) :
    Set.range ((baseChange q).map f).left =
      (pullback.fst V.hom q) ⁻¹' Set.range f.left := by
  change (Set.range ((baseChange q).map f).left : Set ↑(pullback V.hom q)) = _
  rw [baseChange_map_left]
  let : Mono (𝟙 S : S ⟶ S) := inferInstance
  have h := Scheme.Pullback.range_map (f := U.hom) (g := q)
    V.hom q f.left (𝟙 X) (𝟙 S) (by simp) (by simp)
  simp only [Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id,
    Set.range_id, Set.preimage_univ, Set.inter_univ] at h
  convert! h using 1

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual base change preserves the jointly surjective covers of the small étale site. -/
theorem baseChange_coverPreserving :
    CoverPreserving S.smallEtaleTopology X.smallEtaleTopology (baseChange q) where
  cover_preserve {U} {T} hT := by
    obtain ⟨ι, V, f, rfl⟩ := T.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hT
    apply Set.eq_univ_of_forall
    intro z
    have hz : pullback.fst U.hom q z ∈ ⋃ i, Set.range (f i).left := by
      rw [hT]
      trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [baseChange_map_range]
    exact hi

set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-limit preservation holds for arbitrary q, without an étaleness premise. -/
instance baseChange_preservesFiniteLimits : PreservesFiniteLimits (baseChange q) :=
  inferInstanceAs (PreservesFiniteLimits
    (MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale) ⊤ q))

/-- The actual base-change functor is representably flat. -/
instance baseChange_representablyFlat : RepresentablyFlat (baseChange q) :=
  flat_of_preservesFiniteLimits _

/-- The constructed base-change functor is continuous for the actual small étale topologies. -/
instance baseChange_isContinuous :
    (baseChange q).IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_iff_coverPreserving.mpr (baseChange_coverPreserving q)

variable (E : Type u) [Ring E]

/-- The actual direct image q_* on module sheaves, defined by precomposition. -/
def functor :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  (baseChange q).sheafPushforwardContinuous (ModuleCat.{u} E)
    S.smallEtaleTopology X.smallEtaleTopology

/-- The underlying presheaf is literally precomposition by the base-change functor. -/
theorem functor_obj_presheaf (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    ((functor q E).obj F).obj = (baseChange q).op ⋙ F.obj := rfl

/-- At U, direct image evaluates the original sheaf on the actual fiber product U ×[S] X. -/
theorem functor_obj_obj (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) (U : S.Etale) :
    ((functor q E).obj F).obj.obj (op U) =
      F.obj.obj (op (Scheme.Etale.mk (pullback.snd U.hom q))) := rfl

/-- The restriction maps are the original restriction maps along actual base change. -/
theorem functor_obj_map (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    {U V : S.Etale} (f : U ⟶ V) :
    ((functor q E).obj F).obj.map f.op = F.obj.map ((baseChange q).map f).op := rfl

/-- Direct image of a sheaf morphism is evaluated at the same base-changed object. -/
theorem functor_map_app {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)}
    (α : F ⟶ G) (U : S.Etale) :
    ((functor q E).map α).hom.app (op U) = α.hom.app (op ((baseChange q).obj U)) := rfl

/-- The comparison with presheaf precomposition is the actual canonical comparison. -/
def functorCompSheafToPresheafIso :
    functor q E ⋙ sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E) ≅
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} E) ⋙
        (Functor.whiskeringLeft _ _ (ModuleCat.{u} E)).obj (baseChange q).op :=
  (baseChange q).sheafPushforwardContinuousCompSheafToPresheafIso
    (ModuleCat.{u} E) S.smallEtaleTopology X.smallEtaleTopology

/-- The actual direct image is additive on module-sheaf morphisms. -/
instance functor_additive : (functor q E).Additive where
  map_add := by
    intro F G α β
    ext U x
    rfl

/-- The actual direct image preserves finite limits, which are computed on presheaves. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor q E) where
  preservesFiniteLimits J _ _ := by
    let : PreservesLimitsOfShape J
        (functor q E ⋙ sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      preservesLimitsOfShape_of_natIso (functorCompSheafToPresheafIso q E).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (functor q E) (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E))

end PrimeGap182.TypeIII.EtaleDirectImage

#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_obj_left
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_obj_hom
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_map_left
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_map_range
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_coverPreserving
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_representablyFlat
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.baseChange_isContinuous
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_obj_presheaf
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_obj_obj
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_obj_map
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_map_app
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functorCompSheafToPresheafIso
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_additive
#print axioms PrimeGap182.TypeIII.EtaleDirectImage.functor_preservesFiniteLimits
