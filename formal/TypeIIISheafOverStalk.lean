import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected

/-!
# Stalks after restriction to a slice site

Restriction to the slice over an object does not change the stalk at a
chosen lift of a site point.  The comparison is the actual colimit
comparison induced by forgetting a map to that lift.  Constant sheaves
have their prescribed object as stalk, by sheafification invariance and
the colimit of a constant diagram over a connected category.
-/

noncomputable section

universe w v vA u uA

namespace PrimeGap182.TypeIII.SheafOverStalk

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] (Φ : GrothendieckTopology.Point.{w} J)
  {X : C} (x : Φ.fiber.obj X)
  {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{w, w} A]

/-- Forgetting the chosen map to a lifted point on a slice site. -/
def overElementsForget : (Φ.over x).fiber.Elements ⥤ Φ.fiber.Elements :=
  (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).functor ⋙
    Over.forget (Φ.fiber.elementsMk X x)

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor of the lifted neighborhood category is initial. -/
theorem overElementsForget_initial : (overElementsForget Φ x).Initial := by
  let : (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).functor.IsEquivalence :=
    Equivalence.isEquivalence_functor _
  exact Functor.initial_equivalence_comp
    (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).functor
    (Over.forget (Φ.fiber.elementsMk X x))

/-- The actual presheaf stalk on the slice is the original stalk. -/
def presheafOverStalkIso (P : Cᵒᵖ ⥤ A) :
    (Φ.over x).presheafFiber.obj ((Over.forget X).op ⋙ P) ≅
      Φ.presheafFiber.obj P := by
  letI := overElementsForget_initial Φ x
  exact Functor.Final.colimitIso (overElementsForget Φ x).op
    ((CategoryOfElements.π Φ.fiber).op ⋙ P)

/-- The comparison sends a germ in a lifted neighborhood to its original germ. -/
@[reassoc]
theorem presheafOverStalkIso_germ (P : Cᵒᵖ ⥤ A) (U : Over X)
    (u : (Φ.over x).fiber.obj U) :
    (Φ.over x).toPresheafFiber U u ((Over.forget X).op ⋙ P) ≫
        (presheafOverStalkIso Φ x P).hom =
      Φ.toPresheafFiber U.left u.val P := by
  let := overElementsForget_initial Φ x
  exact Functor.Final.ι_colimitIso_hom (overElementsForget Φ x).op
    ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨U, u⟩)

/-- Naturality of the actual slice stalk comparison. -/
@[reassoc]
theorem presheafOverStalkIso_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) :
    (Φ.over x).presheafFiber.map (Functor.whiskerLeft (Over.forget X).op g) ≫
        (presheafOverStalkIso Φ x Q).hom =
      (presheafOverStalkIso Φ x P).hom ≫ Φ.presheafFiber.map g := by
  apply (Φ.over x).presheafFiber_hom_ext
  intro U u
  simp only [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
    Functor.whiskerLeft_app, presheafOverStalkIso_germ_assoc,
    GrothendieckTopology.Point.toPresheafFiber_naturality,
    presheafOverStalkIso_germ]
  rfl

/-- The actual sheaf stalk on the slice is the original sheaf stalk. -/
def sheafOverStalkIso (F : Sheaf J A) :
    (Φ.over x).sheafFiber.obj (F.over X) ≅ Φ.sheafFiber.obj F :=
  presheafOverStalkIso Φ x F.obj

/-- Naturality on actual sheaves. -/
@[reassoc]
theorem sheafOverStalkIso_naturality {F G : Sheaf J A} (g : F ⟶ G) :
    (Φ.over x).sheafFiber.map ((J.overPullback A X).map g) ≫
        (sheafOverStalkIso Φ x G).hom =
      (sheafOverStalkIso Φ x F).hom ≫ Φ.sheafFiber.map g :=
  presheafOverStalkIso_naturality Φ x g.hom

/-- The stalk of a constant presheaf is its constant value. -/
def constantPresheafStalkIso (M : A) :
    Φ.presheafFiber.obj ((Functor.const Cᵒᵖ).obj M) ≅ M :=
  (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙
    (Functor.const Cᵒᵖ).obj M)).coconePointUniqueUpToIso
      (isColimitConstCocone Φ.fiber.Elementsᵒᵖ M)

omit [LocallySmall.{w} C] in
/-- A germ of a constant presheaf is the corresponding constant value. -/
@[reassoc]
theorem constantPresheafStalkIso_germ (M : A) (U : C) (u : Φ.fiber.obj U) :
    Φ.toPresheafFiber U u ((Functor.const Cᵒᵖ).obj M) ≫
        (constantPresheafStalkIso Φ M).hom = 𝟙 M :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙
      (Functor.const Cᵒᵖ).obj M))
    (isColimitConstCocone Φ.fiber.Elementsᵒᵖ M) (op ⟨U, u⟩)

variable [HasProducts.{w} A] [HasWeakSheafify J A]

/-- The actual stalk of the categorical constant sheaf. -/
def constantSheafStalkIso (M : A) :
    Φ.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M :=
  (Φ.presheafToSheafCompSheafFiberIso A).app ((Functor.const Cᵒᵖ).obj M) ≪≫
    constantPresheafStalkIso Φ M

omit [LocallySmall.{w} C] in
/-- The constant-sheaf stalk comparison is normalized on actual germs. -/
@[reassoc]
theorem constantSheafStalkIso_germ (M : A) (U : C) (u : Φ.fiber.obj U) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫
        Φ.toPresheafFiber U u (((constantSheaf J A).obj M).obj) ≫
        (constantSheafStalkIso Φ M).hom = 𝟙 M := by
  change (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫
    Φ.toPresheafFiber U u (sheafify J ((Functor.const Cᵒᵖ).obj M)) ≫
    inv (Φ.presheafFiber.map (toSheafify J ((Functor.const Cᵒᵖ).obj M))) ≫
    (constantPresheafStalkIso Φ M).hom = _
  rw [← GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  rw [IsIso.hom_inv_id_assoc]
  exact constantPresheafStalkIso_germ Φ M U u

/-- A section with values in `M` gives a map from the constant presheaf. -/
def constantPresheafMapOfSection {T : C} (hT : IsTerminal T)
    (M : A) (F : Sheaf J A) (s : M ⟶ F.obj.obj (op T)) :
    (Functor.const Cᵒᵖ).obj M ⟶ F.obj where
  app U := s ≫ F.obj.map (hT.from U.unop).op
  naturality U V g := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    congr 1
    apply congrArg F.obj.map
    apply Quiver.Hom.unop_inj
    exact hT.hom_ext _ _

/-- The map from the categorical constant sheaf defined by an actual section. -/
def constantSheafMapOfSection {T : C} (hT : IsTerminal T)
    (M : A) (F : Sheaf J A) (s : M ⟶ F.obj.obj (op T)) :
    (constantSheaf J A).obj M ⟶ F :=
  ⟨sheafifyLift J (constantPresheafMapOfSection hT M F s) F.property⟩

omit [LocallySmall.{w} C] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A] in
/-- At the terminal object, the constructed map agrees with the given section. -/
theorem constantSheafMapOfSection_unit {T : C} (hT : IsTerminal T)
    (M : A) (F : Sheaf J A) (s : M ⟶ F.obj.obj (op T)) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫
        (constantSheafMapOfSection hT M F s).hom.app (op T) = s := by
  have h := congrArg (fun q => q.app (op T))
    (toSheafify_sheafifyLift J (constantPresheafMapOfSection hT M F s) F.property)
  have hid : hT.from T = 𝟙 T := hT.hom_ext _ _
  have hm : F.obj.map (hT.from T).op = 𝟙 (F.obj.obj (op T)) := by
    rw [hid]
    exact F.obj.map_id (op T)
  change (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫
    (constantSheafMapOfSection hT M F s).hom.app (op T) =
      s ≫ F.obj.map (hT.from T).op at h
  exact h.trans (by rw [hm, Category.comp_id])

omit [LocallySmall.{w} C] in
/-- The actual stalk map is exactly the germ of the section. -/
theorem constantSheafMapOfSection_stalk {T : C} (hT : IsTerminal T)
    (M : A) (F : Sheaf J A) (s : M ⟶ F.obj.obj (op T)) (t : Φ.fiber.obj T) :
    (constantSheafStalkIso Φ M).inv ≫
        Φ.sheafFiber.map (constantSheafMapOfSection hT M F s) =
      s ≫ Φ.toPresheafFiber T t F.obj := by
  let P := (Functor.const Cᵒᵖ).obj M
  let Q := sheafify J P
  let η := toSheafify J P
  let e : Φ.presheafFiber.obj Q ≅ M := constantSheafStalkIso Φ M
  let φ : Q ⟶ F.obj := (constantSheafMapOfSection hT M F s).hom
  have hx : η.app (op T) ≫ Φ.toPresheafFiber T t Q ≫ e.hom = 𝟙 M :=
    constantSheafStalkIso_germ Φ M T t
  have hg : e.inv = η.app (op T) ≫ Φ.toPresheafFiber T t Q := by
    apply (cancel_mono e.hom).mp
    simpa only [Iso.inv_hom_id, Category.assoc] using hx.symm
  have hu : η.app (op T) ≫ φ.app (op T) = s :=
    constantSheafMapOfSection_unit hT M F s
  change e.inv ≫ Φ.presheafFiber.map φ = _
  rw [hg, Category.assoc, GrothendieckTopology.Point.toPresheafFiber_naturality]
  rw [← Category.assoc, hu]

end PrimeGap182.TypeIII.SheafOverStalk

#print axioms PrimeGap182.TypeIII.SheafOverStalk.overElementsForget
#print axioms PrimeGap182.TypeIII.SheafOverStalk.overElementsForget_initial
#print axioms PrimeGap182.TypeIII.SheafOverStalk.presheafOverStalkIso
#print axioms PrimeGap182.TypeIII.SheafOverStalk.presheafOverStalkIso_germ
#print axioms PrimeGap182.TypeIII.SheafOverStalk.presheafOverStalkIso_naturality
#print axioms PrimeGap182.TypeIII.SheafOverStalk.sheafOverStalkIso
#print axioms PrimeGap182.TypeIII.SheafOverStalk.sheafOverStalkIso_naturality
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantPresheafStalkIso
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantPresheafStalkIso_germ
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantSheafStalkIso
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantSheafStalkIso_germ
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantPresheafMapOfSection
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantSheafMapOfSection
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantSheafMapOfSection_unit
#print axioms PrimeGap182.TypeIII.SheafOverStalk.constantSheafMapOfSection_stalk
