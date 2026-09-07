import TypeIIIEtaleSliceSite
import TypeIIISliceLeftKan
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Extension by zero on the small étale site

Restriction to an open object is the actual restriction to its slice site.
Its left adjoint is constructed from the small coproduct left Kan extension
and sheafification.  The stalk comparison is proved using the actual
skyscraper adjunction.  At a point of the open it recovers the original
stalk; at a point outside the open the stalk is zero.

The coefficient category is the category of all modules over a ring, and
the geometric conclusions therefore apply in particular to finite fields
of coefficients.  No assertion about adic coefficients or compactly
supported cohomology is made here.
-/

noncomputable section

universe w v u a b

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace EtaleExtensionByZero

section StalkComparison

variable {C : Type v} [Category.{u} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] (Φ : GrothendieckTopology.Point.{w} J)
  {U : C} (t : Φ.fiber.obj U) [Subsingleton (Φ.fiber.obj U)]
  {A : Type a} [Category.{b} A] [HasProducts.{w} A]

/-- If the fiber of an object is a singleton, its lifted point imposes
no additional condition on fibers of objects of the slice. -/
def overFiberEquiv (V : Over U) :
    Φ.fiber.obj V.left ≃ (Φ.over t).fiber.obj V where
  toFun x := ⟨x, by
    change Φ.fiber.map V.hom x = t
    exact Subsingleton.elim _ _⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv x := Subtype.ext rfl

/-- The product comparison induced by the actual fiber bijection. -/
def overProductIso (V : Over U) (M : A) :
    (∏ᶜ fun _ : Φ.fiber.obj V.left => M) ≅
      (∏ᶜ fun _ : (Φ.over t).fiber.obj V => M) :=
  Pi.whiskerEquiv (overFiberEquiv Φ t V) (fun _ => Iso.refl M)

/-- Restricting a skyscraper to the slice agrees with the skyscraper of
the actual lifted point, by reindexing the defining products. -/
def overSkyscraperIso (M : A) :
    (Φ.skyscraperSheaf M).over U ≅ (Φ.over t).skyscraperSheaf M :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun V => overProductIso Φ t V.unop M)
    (by
      intro V W g
      change Pi.map' (Φ.fiber.map g.unop.left) (fun _ => 𝟙 M) ≫
          (overProductIso Φ t W.unop M).hom =
        (overProductIso Φ t V.unop M).hom ≫
          Pi.map' (f := fun _ : (Φ.over t).fiber.obj V.unop => M)
            (g := fun _ : (Φ.over t).fiber.obj W.unop => M)
            ((Φ.over t).fiber.map g.unop) (fun _ => 𝟙 M)
      apply Pi.hom_ext
      intro x
      simp [overProductIso, Pi.whiskerEquiv, overFiberEquiv]
      rfl)

/-- The skyscraper comparison is natural in the coefficient object. -/
def overSkyscraperFunctorIso :
    Φ.skyscraperSheafFunctor ⋙ J.overPullback A U ≅
      (Φ.over t).skyscraperSheafFunctor :=
  NatIso.ofComponents (overSkyscraperIso Φ t) (by
    intro M N f
    ext V
    change Limits.Pi.map (fun _ : Φ.fiber.obj V.unop.left => f) ≫
        (overProductIso Φ t V.unop N).hom =
      (overProductIso Φ t V.unop M).hom ≫
        Limits.Pi.map (fun _ : (Φ.over t).fiber.obj V.unop => f)
    apply Pi.hom_ext
    intro x
    simp [overProductIso, Pi.whiskerEquiv])

end StalkComparison

section SliceFunctor

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (U : C)
  (A : Type a) [Category.{b} A] [HasCoproducts.{u} A] [HasWeakSheafify J A]

/-- The actual left adjoint to restriction to the slice, using the
proved small-coproduct Kan extension and sheafification. -/
def sliceFunctor : Sheaf (J.over U) A ⥤ Sheaf J A :=
  (Over.forget U).sheafPullback A (J.over U) J

/-- Extension from the slice is left adjoint to actual sheaf restriction. -/
def sliceAdjunction : sliceFunctor J U A ⊣ J.overPullback A U :=
  (Over.forget U).sheafAdjunctionContinuous A (J.over U) J

variable [LocallySmall.{w} C] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
  (Φ : GrothendieckTopology.Point.{w} J)

/-- At a singleton fiber, the extension has the stalk of the original
sheaf at the actual lifted point. -/
def sliceStalkIso (t : Φ.fiber.obj U) [Subsingleton (Φ.fiber.obj U)] :
    sliceFunctor J U A ⋙ Φ.sheafFiber ≅ (Φ.over t).sheafFiber :=
  ((conjugateIsoEquiv
      ((sliceAdjunction J U A).comp Φ.skyscraperSheafAdjunction)
      (Φ.over t).skyscraperSheafAdjunction).symm
    (overSkyscraperFunctorIso Φ t)).symm

omit [LocallySmall.{w} C] in
/-- Outside the object, the extension has zero stalk.  The proof uses
empty products in the actual restricted skyscraper, not a stipulated
support formula. -/
theorem sliceStalk_isZero [HasZeroMorphisms A] [IsEmpty (Φ.fiber.obj U)]
    (F : Sheaf (J.over U) A) :
    IsZero (Φ.sheafFiber.obj ((sliceFunctor J U A).obj F)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (((sliceAdjunction J U A).comp Φ.skyscraperSheafAdjunction).homEquiv F _).injective
  ext V
  apply Pi.hom_ext
  intro x
  exact isEmptyElim (Φ.fiber.map V.unop.hom x)

end SliceFunctor

section GeometricPoints

variable (S : Scheme.{u}) (U : S.Etale) (Ω : Type u)
  [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The literal geometric fiber of an étale object is nonempty exactly
when the image of the geometric point lies in its image in the base. -/
theorem geometricFiber_nonempty_iff :
    Nonempty ((Scheme.pointSmallEtale s).fiber.obj U) ↔
      s default ∈ Set.range U.hom := by
  constructor
  · rintro ⟨t⟩
    let x := Scheme.pointSmallEtaleFiberObjToPreimage s rfl t
    exact ⟨x.val, x.property⟩
  · rintro ⟨x, hx⟩
    obtain ⟨t, _⟩ := Scheme.pointSmallEtaleFiberObjToPreimage_surjective s rfl U ⟨x, hx⟩
    exact ⟨t⟩

/-- A monomorphic étale object has at most one lift of a geometric point. -/
theorem geometricFiber_subsingleton [Mono U.hom] :
    Subsingleton ((Scheme.pointSmallEtale s).fiber.obj U) where
  allEq t r := by
    apply Over.OverMorphism.ext
    apply (cancel_mono U.hom).mp
    exact (Over.w t).trans (Over.w r).symm

end GeometricPoints

section SmallEtale

variable (S : Scheme.{u}) (U : S.Etale) (E : Type u) [Ring E]

/-- The actual equivalence between module sheaves on the slice and on
the small étale site of the étale scheme itself. -/
def sheafEquivalence :
    Sheaf (S.smallEtaleTopology.over U) (ModuleCat.{u} E) ≌
      Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E) := by
  let : (etaleSliceEquiv S U).inverse.IsDenseSubsite
      U.left.smallEtaleTopology (S.smallEtaleTopology.over U) :=
    etaleToSlice_isDenseSubsite S U
  exact (etaleSliceEquiv S U).sheafCongr
    (S.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u} E)

/-- Restriction on the literal small étale sites, through their proved
slice equivalence. -/
def restriction :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E) :=
  S.smallEtaleTopology.overPullback (ModuleCat.{u} E) U ⋙
    (sheafEquivalence S U E).functor

/-- The actual extension functor between the literal small étale sites.
For an open immersion it is extension by zero. -/
def functor :
    Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  (sheafEquivalence S U E).inverse ⋙
    sliceFunctor S.smallEtaleTopology U (ModuleCat.{u} E)

/-- The constructed extension is left adjoint to actual restriction on
the two small étale sites. -/
def adjunction : functor S U E ⊣ restriction S U E :=
  (sheafEquivalence S U E).symm.toAdjunction.comp
    (sliceAdjunction S.smallEtaleTopology U (ModuleCat.{u} E))

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- At every geometric point outside the étale scheme's image, the
actual extension has zero stalk. -/
theorem stalk_isZero (s : Spec (.of Ω) ⟶ S)
    (hs : s default ∉ Set.range U.hom)
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E)) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj ((functor S U E).obj F)) := by
  let : IsEmpty ((Scheme.pointSmallEtale s).fiber.obj U) :=
    ⟨fun t => hs ((geometricFiber_nonempty_iff S U Ω s).mp ⟨t⟩)⟩
  exact sliceStalk_isZero S.smallEtaleTopology U (ModuleCat.{u} E)
    (Scheme.pointSmallEtale s) ((sheafEquivalence S U E).inverse.obj F)

end SmallEtale

section InsideSmallEtale

variable (S : Scheme.{u}) (U : S.Etale) [Mono U.hom]
  (Ω : Type u) [Field Ω] [IsSepClosed Ω] (q : Spec (.of Ω) ⟶ U.left)

/-- A geometric lift over the base is a geometric lift over the open,
by cancellation against its monomorphic structure map. -/
def restrictionFiberEquiv (V : U.left.Etale) :
    (Scheme.pointSmallEtale (q ≫ U.hom)).fiber.obj ((etaleToSlice S U).obj V).left ≃
      (Scheme.pointSmallEtale q).fiber.obj V where
  toFun t := Over.homMk t.left (by
    apply (cancel_mono U.hom).mp
    change (t.left ≫ V.hom) ≫ U.hom = q ≫ U.hom
    exact (Category.assoc t.left V.hom U.hom).trans (Over.w t))
  invFun t := Over.homMk t.left (by
    change t.left ≫ (V.hom ≫ U.hom) = q ≫ U.hom
    exact (Category.assoc t.left V.hom U.hom).symm.trans
      (congrArg (fun f : Spec (.of Ω) ⟶ U.left => f ≫ U.hom) (Over.w t)))
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := Over.OverMorphism.ext rfl

variable (E : Type u) [Ring E]

/-- The product comparison on an actual étale neighborhood of the open. -/
def restrictionProductIso (V : U.left.Etale) (M : ModuleCat.{u} E) :
    (∏ᶜ fun _ : (Scheme.pointSmallEtale (q ≫ U.hom)).fiber.obj
      ((etaleToSlice S U).obj V).left => M) ≅
    (∏ᶜ fun _ : (Scheme.pointSmallEtale q).fiber.obj V => M) :=
  Pi.whiskerEquiv (restrictionFiberEquiv S U Ω q V) (fun _ => Iso.refl M)

/-- On the literal small étale sites, restriction of the base
skyscraper is the skyscraper of the lifted geometric point. -/
def restrictionSkyscraperIso (M : ModuleCat.{u} E) :
    (restriction S U E).obj ((Scheme.pointSmallEtale (q ≫ U.hom)).skyscraperSheaf M) ≅
      (Scheme.pointSmallEtale q).skyscraperSheaf M :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun V => restrictionProductIso S U Ω q E V.unop M)
    (by
      intro V W g
      change Pi.map'
          ((Scheme.pointSmallEtale (q ≫ U.hom)).fiber.map
            ((etaleToSlice S U).map g.unop).left) (fun _ => 𝟙 M) ≫
          (restrictionProductIso S U Ω q E W.unop M).hom =
        (restrictionProductIso S U Ω q E V.unop M).hom ≫
          Pi.map' (f := fun _ : (Scheme.pointSmallEtale q).fiber.obj V.unop => M)
            (g := fun _ : (Scheme.pointSmallEtale q).fiber.obj W.unop => M)
            ((Scheme.pointSmallEtale q).fiber.map g.unop) (fun _ => 𝟙 M)
      apply Pi.hom_ext
      intro x
      simp [restrictionProductIso, Pi.whiskerEquiv, restrictionFiberEquiv]
      rfl)

/-- The actual geometric skyscraper comparison is natural in modules. -/
def restrictionSkyscraperFunctorIso :
    (Scheme.pointSmallEtale (q ≫ U.hom)).skyscraperSheafFunctor ⋙ restriction S U E ≅
      (Scheme.pointSmallEtale q).skyscraperSheafFunctor :=
  NatIso.ofComponents (restrictionSkyscraperIso S U Ω q E) (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    change Limits.Pi.map
        (fun _ : (Scheme.pointSmallEtale (q ≫ U.hom)).fiber.obj
          ((etaleToSlice S U).obj V.unop).left => f) ≫
        (restrictionProductIso S U Ω q E V.unop N).hom =
      (restrictionProductIso S U Ω q E V.unop M).hom ≫
        Limits.Pi.map (fun _ : (Scheme.pointSmallEtale q).fiber.obj V.unop => f)
    apply Pi.hom_ext
    intro x
    simp [restrictionProductIso, Pi.whiskerEquiv])

/-- At a geometric point of an open immersion, the actual extension
has precisely the original sheaf's stalk on the open scheme. -/
def stalkIso :
    functor S U E ⋙ (Scheme.pointSmallEtale (q ≫ U.hom)).sheafFiber ≅
      (Scheme.pointSmallEtale q).sheafFiber :=
  ((conjugateIsoEquiv
      ((adjunction S U E).comp (Scheme.pointSmallEtale (q ≫ U.hom)).skyscraperSheafAdjunction)
      (Scheme.pointSmallEtale q).skyscraperSheafAdjunction).symm
    (restrictionSkyscraperFunctorIso S U Ω q E)).symm

end InsideSmallEtale

end EtaleExtensionByZero

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.overFiberEquiv
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.overProductIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.overSkyscraperIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.overSkyscraperFunctorIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.sliceFunctor
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.sliceAdjunction
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.sliceStalkIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.sliceStalk_isZero
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.geometricFiber_nonempty_iff
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.geometricFiber_subsingleton
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.sheafEquivalence
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.restriction
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.functor
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.adjunction
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.stalk_isZero
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.restrictionFiberEquiv
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.restrictionProductIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.restrictionSkyscraperIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.restrictionSkyscraperFunctorIso
#print axioms PrimeGap182.TypeIII.EtaleExtensionByZero.stalkIso
