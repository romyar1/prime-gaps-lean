import TypeIIIEtaleSkyscraperExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Products of actual étale skyscrapers

For a small family of actual points, the diagram of the original stalks
is left adjoint to the product of the original skyscrapers.  Exactness
of this right adjoint is proved on each étale object by two products of
module maps.  This argument does not require products of arbitrary
epimorphisms of sheaves to be epimorphisms.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleSkyscraperFamily

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) {ι : Type u}
  (Φ : ι → GrothendieckTopology.Point.{u} S.smallEtaleTopology)
  (E : Type u) [Ring E]

/-- The diagram consisting of the original stalk at each point. -/
def stalks : Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤
    (Discrete ι ⥤ ModuleCat.{u} E) where
  obj F := Discrete.functor (fun i => (Φ i).sheafFiber.obj F)
  map f := Discrete.natTrans (fun i => (Φ i.as).sheafFiber.map f)

/-- Evaluation at a family index is the original stalk functor. -/
def stalksEvaluationIso (i : ι) :
    stalks S Φ E ⋙ (evaluation (Discrete ι) (ModuleCat.{u} E)).obj ⟨i⟩ ≅
      (Φ i).sheafFiber := NatIso.ofComponents (fun _ => Iso.refl _)

/-- The family of original skyscraper sheaves for a coefficient diagram. -/
def skyscrapers (M : Discrete ι ⥤ ModuleCat.{u} E) :
    ι → Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  fun i => (EtaleSkyscraper.functor S (Φ i) E).obj (M.obj ⟨i⟩)

/-- The actual product of the original skyscrapers, with the original maps. -/
def functor : (Discrete ι ⥤ ModuleCat.{u} E) ⥤
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) where
  obj M := ∏ᶜ skyscrapers S Φ E M
  map {M N} f := Limits.Pi.map (f := skyscrapers S Φ E M) (g := skyscrapers S Φ E N)
    (fun i => (EtaleSkyscraper.functor S (Φ i) E).map (f.app ⟨i⟩))
  map_id M := by
    simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]
    exact Limits.Pi.map_id (f := skyscrapers S Φ E M)
  map_comp f g := by
    simp only [NatTrans.comp_app, Functor.map_comp]
    exact (Limits.Pi.map_comp_map _ _).symm

/-- The product map has the specified original skyscraper components. -/
@[reassoc (attr := simp)]
theorem functor_map_π {M N : Discrete ι ⥤ ModuleCat.{u} E} (f : M ⟶ N) (i : ι) :
    (functor S Φ E).map f ≫ Pi.π (skyscrapers S Φ E N) i =
      Pi.π (skyscrapers S Φ E M) i ≫
        (EtaleSkyscraper.functor S (Φ i) E).map (f.app ⟨i⟩) := by
  exact Limits.Pi.map_π (f := skyscrapers S Φ E M) (g := skyscrapers S Φ E N)
    (fun j => (EtaleSkyscraper.functor S (Φ j) E).map (f.app ⟨j⟩)) i

set_option backward.isDefEq.respectTransparency false in
/-- The product universal property combined with the original stalk adjunctions. -/
def homEquiv (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    (M : Discrete ι ⥤ ModuleCat.{u} E) :
    ((stalks S Φ E).obj F ⟶ M) ≃ (F ⟶ (functor S Φ E).obj M) where
  toFun f := Pi.lift (fun i =>
    (EtaleSkyscraper.adjunction S (Φ i) E).homEquiv F (M.obj ⟨i⟩) (f.app ⟨i⟩))
  invFun f := Discrete.natTrans (fun i =>
    ((EtaleSkyscraper.adjunction S (Φ i.as) E).homEquiv F (M.obj i)).symm
      (f ≫ Pi.π (skyscrapers S Φ E M) i.as))
  left_inv f := by
    ext i
    simp
  right_inv f := by
    apply Pi.hom_ext
    intro i
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual family stalk functor is left adjoint to the skyscraper product. -/
def adjunction : stalks S Φ E ⊣ functor S Φ E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv S Φ E
      homEquiv_naturality_left_symm := fun f g => by
        apply NatTrans.ext
        funext i
        dsimp [homEquiv, stalks]
        rw [assoc]
        exact (EtaleSkyscraper.adjunction S (Φ i.as) E).homEquiv_naturality_left_symm
          f (g ≫ Pi.π _ i.as)
      homEquiv_naturality_right := fun f g => by
        apply Pi.hom_ext
        intro i
        simp only [homEquiv, Equiv.coe_fn_mk, NatTrans.comp_app, Pi.lift_π,
          assoc, functor_map_π, Pi.lift_π_assoc]
        exact (EtaleSkyscraper.adjunction S (Φ i) E).homEquiv_naturality_right
          (f.app ⟨i⟩) (g.app ⟨i⟩) }

/-- Every family of stalks preserves finite limits component by component. -/
instance stalks_preservesFiniteLimits : PreservesFiniteLimits (stalks S Φ E) :=
  preservesFiniteLimits_of_evaluation _ (fun i =>
    preservesFiniteLimits_of_natIso (stalksEvaluationIso S Φ E i.as).symm)

/-- Every family of stalks preserves finite colimits component by component. -/
instance stalks_preservesFiniteColimits : PreservesFiniteColimits (stalks S Φ E) :=
  preservesFiniteColimits_of_evaluation _ (fun i =>
    preservesFiniteColimits_of_natIso (stalksEvaluationIso S Φ E i.as).symm)

/-- The actual product functor is a right adjoint. -/
instance functor_isRightAdjoint : (functor S Φ E).IsRightAdjoint :=
  (adjunction S Φ E).isRightAdjoint

/-- Its finite limits are preserved by the original product adjunction. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor S Φ E) :=
  inferInstance

/-- The maps of the actual product functor are additive. -/
instance functor_additive : (functor S Φ E).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option backward.isDefEq.respectTransparency false in
/-- On every étale object, the map is a nested product of the original
surjective module maps; therefore the resulting sheaf morphism is epi. -/
instance functor_preservesEpimorphisms : (functor S Φ E).PreservesEpimorphisms where
  preserves {M N} f hf := by
    have hU : ∀ U, Epi (((functor S Φ E).map f).hom.app U) := by
      intro U
      let ev := sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u} E) ⋙
        (evaluation S.Etaleᵒᵖ (ModuleCat.{u} E)).obj U
      have hinner : ∀ i : ι,
          Epi (ev.map ((EtaleSkyscraper.functor S (Φ i) E).map (f.app ⟨i⟩))) := by
        intro i
        let τ : Discrete.functor (fun (_ : (Φ i).fiber.obj U.unop) => M.obj ⟨i⟩) ⟶
            Discrete.functor (fun (_ : (Φ i).fiber.obj U.unop) => N.obj ⟨i⟩) :=
          Discrete.natTrans (fun _ => f.app ⟨i⟩)
        have hi : Epi (f.app ⟨i⟩) := inferInstance
        have : ∀ j, Epi (τ.app j) := fun _ => hi
        have : Epi τ := NatTrans.epi_of_epi_app τ
        change Epi ((lim (J := Discrete ((Φ i).fiber.obj U.unop))
          (C := ModuleCat.{u} E)).map τ)
        exact Functor.map_epi _ τ
      let τ : Discrete.functor (fun i => ev.obj (skyscrapers S Φ E M i)) ⟶
          Discrete.functor (fun i => ev.obj (skyscrapers S Φ E N i)) :=
        Discrete.natTrans (fun i =>
          ev.map ((EtaleSkyscraper.functor S (Φ i.as) E).map (f.app i)))
      have : ∀ i, Epi (τ.app i) := fun i => hinner i.as
      have : Epi τ := NatTrans.epi_of_epi_app τ
      have houter : Epi (Limits.Pi.map
          (f := fun i => ev.obj (skyscrapers S Φ E M i))
          (g := fun i => ev.obj (skyscrapers S Φ E N i)) (fun i =>
          ev.map ((EtaleSkyscraper.functor S (Φ i) E).map (f.app ⟨i⟩)))) :=
        Functor.map_epi (lim (J := Discrete ι) (C := ModuleCat.{u} E)) τ
      change Epi (ev.map ((functor S Φ E).map f))
      rw [← epi_comp_iff_of_isIso _ (piComparison ev (skyscrapers S Φ E N))]
      have hw : ev.map ((functor S Φ E).map f) ≫
          piComparison ev (skyscrapers S Φ E N) =
          piComparison ev (skyscrapers S Φ E M) ≫ Limits.Pi.map
            (f := fun i => ev.obj (skyscrapers S Φ E M i))
            (g := fun i => ev.obj (skyscrapers S Φ E N i)) (fun i =>
            ev.map ((EtaleSkyscraper.functor S (Φ i) E).map (f.app ⟨i⟩))) := by
        apply Pi.hom_ext
        intro i
        simp only [assoc, piComparison_comp_π, Limits.Pi.map_π, piComparison_comp_π_assoc,
          ← ev.map_comp, functor_map_π]
      rw [hw]
      infer_instance
    have : Epi ((functor S Φ E).map f).hom := NatTrans.epi_of_epi_app _
    exact Sheaf.Hom.epi_of_presheaf_epi S.smallEtaleTopology (ModuleCat.{u} E) _

/-- The actual product of skyscrapers is exact. -/
instance functor_preservesHomology : (functor S Φ E).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The actual product functor preserves finite colimits. -/
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor S Φ E) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Injective diagrams give injective products, using the exact family stalk adjunction. -/
instance functor_preservesInjectiveObjects : (functor S Φ E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (adjunction S Φ E)

/-- Every actual short exact sequence of coefficient diagrams remains short exact. -/
theorem map_shortExact (T : ShortComplex (Discrete ι ⥤ ModuleCat.{u} E))
    (hT : T.ShortExact) : (T.map (functor S Φ E)).ShortExact :=
  hT.map_of_exact (functor S Φ E)

#print axioms stalks
#print axioms stalksEvaluationIso
#print axioms skyscrapers
#print axioms functor
#print axioms functor_map_π
#print axioms functor_map_π_assoc
#print axioms homEquiv
#print axioms adjunction
#print axioms stalks_preservesFiniteLimits
#print axioms stalks_preservesFiniteColimits
#print axioms functor_isRightAdjoint
#print axioms functor_preservesFiniteLimits
#print axioms functor_additive
#print axioms functor_preservesEpimorphisms
#print axioms functor_preservesHomology
#print axioms functor_preservesFiniteColimits
#print axioms functor_preservesInjectiveObjects
#print axioms map_shortExact

end PrimeGap182.TypeIII.EtaleSkyscraperFamily
