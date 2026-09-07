import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Left Kan extension from a slice using small coproducts

For a presheaf P on Over U, its left Kan extension along
(Over.forget U).op has value at V given by the coproduct of P(V,a)
over all arrows a : V → U. The indexing type lies in the hom universe
of C, even when the object universe of C is larger.

The construction and its universal property below use only these
coproducts. In particular, they require no colimits indexed by a large
comma category and no flatness assumption on the forgetful functor.
-/

noncomputable section

universe u v w z

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

variable {C : Type v} [Category.{u} C] (U : C)
  {A : Type w} [Category.{z} A] [HasCoproducts.{u} A]
  (P : (Over U)ᵒᵖ ⥤ A)

/-- The extension value is a coproduct indexed only by a hom set. -/
abbrev sliceLeftKanObj (V : Cᵒᵖ) : A :=
  ∐ fun a : V.unop ⟶ U => P.obj (op (Over.mk a))

/-- Restriction takes the a summand to the summand indexed by its
precomposition and applies the actual presheaf map in the slice. -/
def sliceLeftKanMap {V W : Cᵒᵖ} (f : V ⟶ W) :
    sliceLeftKanObj U P V ⟶ sliceLeftKanObj U P W :=
  Sigma.desc fun a =>
    P.map ((Over.homMk f.unop rfl : Over.mk (f.unop ≫ a) ⟶ Over.mk a).op) ≫
      Sigma.ι (fun b : W.unop ⟶ U => P.obj (op (Over.mk b))) (f.unop ≫ a)

/-- A summand formula with an arbitrary presentation of the composite
index; it also handles the associativity identifications of indices. -/
theorem sliceLeftKanMap_ι {V W : Cᵒᵖ} (f : V ⟶ W)
    (a : V.unop ⟶ U) (b : W.unop ⟶ U) (h : f.unop ≫ a = b) :
    Sigma.ι (fun c : V.unop ⟶ U => P.obj (op (Over.mk c))) a ≫
        sliceLeftKanMap U P f =
      P.map ((Over.homMk f.unop h : Over.mk b ⟶ Over.mk a).op) ≫
        Sigma.ι (fun c : W.unop ⟶ U => P.obj (op (Over.mk c))) b := by
  subst b
  exact Sigma.ι_desc _ a

/-- The explicit restriction map respects identity arrows. -/
theorem sliceLeftKanMap_id (V : Cᵒᵖ) :
    sliceLeftKanMap U P (𝟙 V) = 𝟙 (sliceLeftKanObj U P V) := by
  apply Sigma.hom_ext
  intro a
  rw [sliceLeftKanMap_ι U P (𝟙 V) a a (by simp)]
  have h : (Over.homMk (𝟙 V).unop (by simp) : Over.mk a ⟶ Over.mk a) =
      𝟙 (Over.mk a) := by
    apply Over.OverMorphism.ext
    rfl
  rw [h, op_id, Functor.map_id, Category.id_comp, Category.comp_id]

/-- The explicit restriction map respects composition. -/
theorem sliceLeftKanMap_comp {V W X : Cᵒᵖ} (f : V ⟶ W) (g : W ⟶ X) :
    sliceLeftKanMap U P (f ≫ g) = sliceLeftKanMap U P f ≫ sliceLeftKanMap U P g := by
  apply Sigma.hom_ext
  intro a
  let b : W.unop ⟶ U := f.unop ≫ a
  let c : X.unop ⟶ U := g.unop ≫ b
  have h : (f ≫ g).unop ≫ a = c := by
    dsimp [b, c]
    simp only [Category.assoc]
  rw [sliceLeftKanMap_ι U P (f ≫ g) a c h, ← Category.assoc,
    sliceLeftKanMap_ι U P f a b rfl, Category.assoc,
    sliceLeftKanMap_ι U P g b c rfl, ← Category.assoc, ← P.map_comp]
  congr 1

/-- The actual presheaf formed from the explicit slice coproducts. -/
def sliceLeftKan : Cᵒᵖ ⥤ A where
  obj := sliceLeftKanObj U P
  map f := sliceLeftKanMap U P f
  map_id := sliceLeftKanMap_id U P
  map_comp f g := sliceLeftKanMap_comp U P f g

/-- The unit includes the presheaf value into its own coordinate summand. -/
def sliceLeftKanUnit : P ⟶ (Over.forget U).op ⋙ sliceLeftKan U P where
  app X := Sigma.ι
    (fun a : X.unop.left ⟶ U => P.obj (op (Over.mk a))) X.unop.hom
  naturality {X Y} f := by
    change P.map f ≫
        Sigma.ι (fun a : Y.unop.left ⟶ U => P.obj (op (Over.mk a))) Y.unop.hom =
      Sigma.ι (fun a : X.unop.left ⟶ U => P.obj (op (Over.mk a))) X.unop.hom ≫
        sliceLeftKanMap U P f.unop.left.op
    simpa only [Quiver.Hom.unop_op, Over.homMk_eta, Quiver.Hom.op_unop] using
      (sliceLeftKanMap_ι U P f.unop.left.op X.unop.hom Y.unop.hom
        (Over.w f.unop)).symm

/-- The actual map to any proposed extension is defined separately on
each coordinate summand by the given transformation. -/
def sliceLeftKanDesc (G : Cᵒᵖ ⥤ A) (β : P ⟶ (Over.forget U).op ⋙ G) :
    sliceLeftKan U P ⟶ G where
  app V := Sigma.desc fun a : V.unop ⟶ U => β.app (op (Over.mk a))
  naturality {V W} f := by
    apply Sigma.hom_ext
    intro a
    change Sigma.ι (fun b : V.unop ⟶ U => P.obj (op (Over.mk b))) a ≫
        sliceLeftKanMap U P f ≫
          (Sigma.desc fun b : W.unop ⟶ U => β.app (op (Over.mk b))) =
      Sigma.ι (fun b : V.unop ⟶ U => P.obj (op (Over.mk b))) a ≫
        (Sigma.desc fun b : V.unop ⟶ U => β.app (op (Over.mk b))) ≫ G.map f
    rw [← Category.assoc, sliceLeftKanMap_ι U P f a (f.unop ≫ a) rfl,
      Category.assoc, Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc]
    exact β.naturality
      ((Over.homMk f.unop rfl : Over.mk (f.unop ≫ a) ⟶ Over.mk a).op)

/-- The induced map takes each coordinate inclusion to the prescribed
component of the transformation. -/
theorem sliceLeftKanDesc_ι (G : Cᵒᵖ ⥤ A) (β : P ⟶ (Over.forget U).op ⋙ G)
    (V : Cᵒᵖ) (a : V.unop ⟶ U) :
    Sigma.ι (fun b : V.unop ⟶ U => P.obj (op (Over.mk b))) a ≫
      (sliceLeftKanDesc U P G β).app V = β.app (op (Over.mk a)) :=
  Sigma.ι_desc _ a

/-- The factorization through the unit is exactly the proposed extension map. -/
theorem sliceLeftKanDesc_fac (G : Cᵒᵖ ⥤ A) (β : P ⟶ (Over.forget U).op ⋙ G) :
    sliceLeftKanUnit U P ≫ whiskerLeft (Over.forget U).op (sliceLeftKanDesc U P G β) =
      β := by
  ext X
  exact Sigma.ι_desc _ X.unop.hom

/-- A map from the coproduct presheaf is determined by its restriction
along the actual unit. -/
theorem sliceLeftKan_hom_ext {G : Cᵒᵖ ⥤ A} (η θ : sliceLeftKan U P ⟶ G)
    (h : sliceLeftKanUnit U P ≫ whiskerLeft (Over.forget U).op η =
      sliceLeftKanUnit U P ≫ whiskerLeft (Over.forget U).op θ) : η = θ := by
  ext V
  apply Sigma.hom_ext
  intro a
  exact NatTrans.congr_app h (op (Over.mk a))

/-- The explicit coproduct construction satisfies the actual categorical
universal property of left Kan extension. -/
instance sliceLeftKan_isLeftKanExtension :
    (sliceLeftKan U P).IsLeftKanExtension (sliceLeftKanUnit U P) where
  nonempty_isUniversal := ⟨IsInitial.ofUniqueHom
    (fun T => StructuredArrow.homMk (sliceLeftKanDesc U P T.right T.hom)
      (sliceLeftKanDesc_fac U P T.right T.hom))
    (by
      intro T η
      apply StructuredArrow.hom_ext
      apply sliceLeftKan_hom_ext U P
      change sliceLeftKanUnit U P ≫ whiskerLeft (Over.forget U).op η.right =
        sliceLeftKanUnit U P ≫
          whiskerLeft (Over.forget U).op (sliceLeftKanDesc U P T.right T.hom)
      rw [sliceLeftKanDesc_fac]
      exact StructuredArrow.w η)⟩

/-- Left Kan extension along the opposite of the actual slice forgetful
functor exists from coproducts in the hom universe alone. -/
instance overForget_op_hasLeftKanExtension :
    Functor.HasLeftKanExtension (Over.forget U).op P :=
  Functor.HasLeftKanExtension.mk (sliceLeftKan U P) (sliceLeftKanUnit U P)

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.sliceLeftKanObj
#print axioms PrimeGap182.TypeIII.sliceLeftKanMap
#print axioms PrimeGap182.TypeIII.sliceLeftKanMap_ι
#print axioms PrimeGap182.TypeIII.sliceLeftKanMap_id
#print axioms PrimeGap182.TypeIII.sliceLeftKanMap_comp
#print axioms PrimeGap182.TypeIII.sliceLeftKan
#print axioms PrimeGap182.TypeIII.sliceLeftKanUnit
#print axioms PrimeGap182.TypeIII.sliceLeftKanDesc
#print axioms PrimeGap182.TypeIII.sliceLeftKanDesc_ι
#print axioms PrimeGap182.TypeIII.sliceLeftKanDesc_fac
#print axioms PrimeGap182.TypeIII.sliceLeftKan_hom_ext
#print axioms PrimeGap182.TypeIII.sliceLeftKan_isLeftKanExtension
#print axioms PrimeGap182.TypeIII.overForget_op_hasLeftKanExtension
