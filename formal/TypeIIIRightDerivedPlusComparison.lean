import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Comparing ordinary right derived functors with the bounded below derived functor

The comparison uses the existing injective resolution and its existing extension
to an integer-indexed complex.  The canonical derived-functor unit at that
degreewise-injective complex gives the comparison.  No acyclicity assumption on
another class of objects or preservation of injectives by another functor is used.
-/

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂ s₁ s₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

section Extension

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  {ι : Type s₁} {ι' : Type s₂} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- Applying an additive functor commutes with the objects in a zero extension. -/
def mapExtendComplexXIso (K : HomologicalComplex C c) (i : Option ι) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero D)
  | some _ => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The actual complex obtained by mapping a zero extension is canonically
isomorphic to the zero extension of the mapped complex. -/
def mapExtendComplexIso (K : HomologicalComplex C c) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => mapExtendComplexXIso F K (e.r i)) ?_
  intro i j _
  have h (x y : Option ι) :
      (mapExtendComplexXIso F K x).hom ≫
          HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) x y =
        F.map (HomologicalComplex.extend.d K x y) ≫
          (mapExtendComplexXIso F K y).hom := by
    cases x <;> cases y <;>
      simp [mapExtendComplexXIso, HomologicalComplex.extend.d]
  exact h (e.r i) (e.r j)

set_option backward.isDefEq.respectTransparency false in
/-- The zero-extension comparison respects the literal maps of complexes. -/
theorem mapExtendComplexIso_naturality {K L : HomologicalComplex C c}
    (φ : K ⟶ L) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (mapExtendComplexIso F L e).hom =
      (mapExtendComplexIso F K e).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i
  have h (x : Option ι) :
      F.map (HomologicalComplex.extend.mapX φ x) ≫ (mapExtendComplexXIso F L x).hom =
        (mapExtendComplexXIso F K x).hom ≫
          HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) x := by
    cases x <;> simp [mapExtendComplexXIso, HomologicalComplex.extend.mapX]
  exact h (e.r i)

/-- The comparison of zero extensions is natural in the complex. -/
def mapExtendFunctorIso (e : c.Embedding c') :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (fun K => mapExtendComplexIso F K e)
    (fun φ => mapExtendComplexIso_naturality F φ e)

set_option backward.isDefEq.respectTransparency false in
/-- In a retained degree, the extension comparison uses the original component
isomorphism and its image under `F`. -/
theorem mapExtendComplexIso_hom_f_comp (K : HomologicalComplex C c)
    (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendComplexIso F K e).hom.f i' ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
      F.map (K.extendXIso e h).hom := by
  have h' (x : Option ι) (hx : x = some i) :
      (mapExtendComplexXIso F K x).hom ≫
          (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) hx).hom =
        F.map (HomologicalComplex.extend.XIso K hx).hom := by
    subst x
    simp [mapExtendComplexXIso, HomologicalComplex.extend.XIso]
  exact h' (e.r i') (e.r_eq_some h)

/-- The existing homology comparison for an extension, assembled naturally. -/
def extendHomologyFunctorIso (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i') :
    e.extendFunctor C ⋙ HomologicalComplex.homologyFunctor C c' i' ≅
      HomologicalComplex.homologyFunctor C c i :=
  NatIso.ofComponents (fun K => K.extendHomologyIso e h)
    (fun φ => HomologicalComplex.extendHomologyIso_hom_naturality φ e h)

set_option backward.isDefEq.respectTransparency false in
/-- Applying an additive functor to a quotient morphism in the bounded below
homotopy category is the quotient of the actual mapped complex morphism. -/
theorem mapCochainPlusQuotient_map {K L : CochainComplex.Plus C} (φ : K ⟶ L) :
    F.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map φ) =
      (HomotopyCategory.Plus.quotient D).map (F.mapCochainComplexPlus.map φ) := rfl

end Extension

section Resolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Homology in degree zero of a map from a single object to an extended
nonnegative complex is determined by the actual map to cycles. -/
theorem singleToExtendedHomology_zero {A : C} (K : CochainComplex C ℕ)
    (g : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶
      K.extend ComplexShape.embeddingUpNat)
    (u : A ⟶ K.cycles 0)
    (hu : u ≫ K.iCycles 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ g.f 0 ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
        HomologicalComplex.homologyMap g 0 ≫
          (K.extendHomologyIso ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom =
      u ≫ K.homologyπ 0 := by
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (.up ℤ) 0 A,
    assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom]
  have hc :
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).inv ≫
          HomologicalComplex.cyclesMap g 0 ≫
            (K.extendCyclesIso ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom = u := by
    rw [← cancel_mono (K.iCycles 0)]
    simp only [assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i_assoc,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc, hu]
  simpa only [assoc] using congrArg (fun z => z ≫ K.homologyπ 0) hc

/-- The literal zero extension embeds every nonnegative complex in the bounded
below category. -/
def nonnegativeCochainPlus : CochainComplex C ℕ ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (ComplexShape.embeddingUpNat.extendFunctor C)
    (fun K => ⟨0, inferInstanceAs (CochainComplex.IsStrictlyGE
      (K.extend ComplexShape.embeddingUpNat) 0)⟩)

/-- The original integer extension of an injective resolution, in the bounded
below category. -/
abbrev injectiveResolutionCochainPlus {A : C} (I : InjectiveResolution A) :
    CochainComplex.Plus C :=
  ⟨I.cochainComplex, 0, inferInstance⟩

/-- A single object in degree zero as an actual bounded below complex. -/
abbrev singleZeroCochainPlus (A : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩

/-- The original augmentation `I.ι'`, regarded as a map of bounded below complexes. -/
def injectiveResolutionPlusAugmentation {A : C} (I : InjectiveResolution A) :
    singleZeroCochainPlus A ⟶ injectiveResolutionCochainPlus I :=
  ObjectProperty.homMk I.ι'

variable [HasDerivedCategory.{w₁} C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual augmentation becomes an isomorphism after localization. -/
def injectiveResolutionDerivedPlusIso {A : C} (I : InjectiveResolution A) :
    (DerivedCategory.Plus.singleFunctor C 0).obj A ≅
      DerivedCategory.Plus.Q.obj (injectiveResolutionCochainPlus I) := by
  have hi : HomotopyCategory.Plus.quasiIso C
      ((HomotopyCategory.Plus.quotient C).map (injectiveResolutionPlusAugmentation I)) := by
    change HomotopyCategory.quasiIso C (.up ℤ)
      ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff I.ι').2
      (inferInstanceAs (QuasiIso I.ι'))
  have : IsIso (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient C).map (injectiveResolutionPlusAugmentation I))) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _ hi
  exact asIso (DerivedCategory.Plus.Qh.map
    ((HomotopyCategory.Plus.quotient C).map (injectiveResolutionPlusAugmentation I)))

/-- The forward map is the localization of the original augmentation. -/
theorem injectiveResolutionDerivedPlusIso_hom {A : C} (I : InjectiveResolution A) :
    (injectiveResolutionDerivedPlusIso I).hom =
      DerivedCategory.Plus.Q.map (injectiveResolutionPlusAugmentation I) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Localization of the original augmentation respects actual maps of resolutions. -/
theorem injectiveResolutionDerivedPlusIso_naturality {A B : C}
    {I : InjectiveResolution A} {J : InjectiveResolution B} {f : A ⟶ B}
    (φ : I.Hom J f) :
    (DerivedCategory.Plus.singleFunctor C 0).map f ≫
        (injectiveResolutionDerivedPlusIso J).hom =
      (injectiveResolutionDerivedPlusIso I).hom ≫
        DerivedCategory.Plus.Q.map ((nonnegativeCochainPlus (C := C)).map φ.hom) := by
  change DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk ((CochainComplex.singleFunctor C 0).map f)) ≫
        DerivedCategory.Plus.Q.map (injectiveResolutionPlusAugmentation J) =
      DerivedCategory.Plus.Q.map (injectiveResolutionPlusAugmentation I) ≫
        DerivedCategory.Plus.Q.map ((nonnegativeCochainPlus (C := C)).map φ.hom)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply DerivedCategory.Plus.Q.congr_map
  apply (CochainComplex.Plus.ι C).map_injective
  exact φ.ι'_comp_hom'.symm

set_option backward.isDefEq.respectTransparency false in
/-- Homology in the bounded below derived category is the original complex
homology after applying the localization functor. -/
def cochainPlusHomologyFunctorIso (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
        (DerivedCategory.quotientCompQhIso C)) (DerivedCategory.homologyFunctor C n) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
      (DerivedCategory.homologyFunctorFactors C n)

end Resolution

section Derived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- The existing RF-plus unit at the original integer extension of `I`,
followed by the inverse of the original augmentation, computes RF-plus on `A`. -/
def rightDerivedPlusResolutionIso {A : C} (I : InjectiveResolution A) :
    DerivedCategory.Plus.Q.obj
        (F.mapCochainComplexPlus.obj (injectiveResolutionCochainPlus I)) ≅
      F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A) :=
  asIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus I))) ≪≫
    F.rightDerivedFunctorPlus.mapIso (injectiveResolutionDerivedPlusIso I).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The RF-plus computation respects each actual map of the original resolutions. -/
theorem rightDerivedPlusResolutionIso_naturality {A B : C}
    {I : InjectiveResolution A} {J : InjectiveResolution B} {f : A ⟶ B}
    (φ : I.Hom J f) :
    DerivedCategory.Plus.Q.map
        (F.mapCochainComplexPlus.map ((nonnegativeCochainPlus (C := C)).map φ.hom)) ≫
          (rightDerivedPlusResolutionIso F J).hom =
      (rightDerivedPlusResolutionIso F I).hom ≫
        F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) := by
  have h := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map
      ((nonnegativeCochainPlus (C := C)).map φ.hom))
  have h' :
      DerivedCategory.Plus.Q.map
          (F.mapCochainComplexPlus.map ((nonnegativeCochainPlus (C := C)).map φ.hom)) ≫
        F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus J)) =
      F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus I)) ≫
        F.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map ((nonnegativeCochainPlus (C := C)).map φ.hom)) := by
    dsimp only [Functor.comp_map] at h
    rw [mapCochainPlusQuotient_map] at h
    exact h
  have ha := injectiveResolutionDerivedPlusIso_naturality φ
  have ha' :
      DerivedCategory.Plus.Q.map ((nonnegativeCochainPlus (C := C)).map φ.hom) ≫
          (injectiveResolutionDerivedPlusIso J).inv =
        (injectiveResolutionDerivedPlusIso I).inv ≫
          (DerivedCategory.Plus.singleFunctor C 0).map f := by
    rw [← cancel_mono (injectiveResolutionDerivedPlusIso J).hom]
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [ha, Iso.inv_hom_id_assoc]
  change
    DerivedCategory.Plus.Q.map
        (F.mapCochainComplexPlus.map ((nonnegativeCochainPlus (C := C)).map φ.hom)) ≫
      (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus J)) ≫
        F.rightDerivedFunctorPlus.map (injectiveResolutionDerivedPlusIso J).inv) =
    (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus I)) ≫
      F.rightDerivedFunctorPlus.map (injectiveResolutionDerivedPlusIso I).inv) ≫
        F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)
  rw [← assoc, h', assoc, ← Functor.map_comp, ha', Functor.map_comp, assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The computation isomorphism intertwines the actual augmentation with
the original RF-plus unit. -/
theorem rightDerivedPlusResolutionIso_augmentation {A : C} (I : InjectiveResolution A) :
    DerivedCategory.Plus.Q.map
        (F.mapCochainComplexPlus.map (injectiveResolutionPlusAugmentation I)) ≫
          (rightDerivedPlusResolutionIso F I).hom =
      F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A) := by
  have h := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map (injectiveResolutionPlusAugmentation I))
  dsimp only [Functor.comp_map] at h
  rw [mapCochainPlusQuotient_map] at h
  have h' :
      DerivedCategory.Plus.Q.map
          (F.mapCochainComplexPlus.map (injectiveResolutionPlusAugmentation I)) ≫
        F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus I)) =
      F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A) ≫
        F.rightDerivedFunctorPlus.map (injectiveResolutionDerivedPlusIso I).hom := h
  change DerivedCategory.Plus.Q.map
      (F.mapCochainComplexPlus.map (injectiveResolutionPlusAugmentation I)) ≫
    (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient C).obj (injectiveResolutionCochainPlus I)) ≫
      F.rightDerivedFunctorPlus.map (injectiveResolutionDerivedPlusIso I).inv) =
    F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A)
  rw [← assoc, h', assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [F.rightDerivedFunctorPlus.map_id]
  exact CategoryTheory.Category.comp_id
    (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))

set_option backward.isDefEq.respectTransparency false in
/-- Mapping, zero extension and derived-category homology commute naturally
on all nonnegative complexes. -/
def mappedNonnegativeComplexHomologyIso (n : ℕ) :
    nonnegativeCochainPlus (C := C) ⋙ F.mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor D (n : ℤ) ≅
      F.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.homologyFunctor D (.up ℕ) n :=
  Functor.isoWhiskerLeft (nonnegativeCochainPlus (C := C) ⋙ F.mapCochainComplexPlus)
      (cochainPlusHomologyFunctorIso (C := D) (n : ℤ)) ≪≫
    Functor.isoWhiskerRight (mapExtendFunctorIso F ComplexShape.embeddingUpNat)
      (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℕ))
      (extendHomologyFunctorIso (C := D) ComplexShape.embeddingUpNat (i := n) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical homology comparisons return from the same integer extension
to the original nonnegative injective-resolution complex. -/
def mappedResolutionPlusHomologyIso {A : C} (I : InjectiveResolution A) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
        (DerivedCategory.Plus.Q.obj
          (F.mapCochainComplexPlus.obj (injectiveResolutionCochainPlus I))) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  (mappedNonnegativeComplexHomologyIso F n).app I.cocomplex

omit [EnoughInjectives C] [HasDerivedCategory C] in
/-- The component consists of the existing localization, mapping and extension
homology comparisons, in their actual order. -/
theorem mappedResolutionPlusHomologyIso_hom {A : C} (I : InjectiveResolution A) (n : ℕ) :
    (mappedResolutionPlusHomologyIso F I n).hom =
      (cochainPlusHomologyFunctorIso (C := D) (n : ℤ)).hom.app
          (F.mapCochainComplexPlus.obj (injectiveResolutionCochainPlus I)) ≫
        (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).map
          (mapExtendComplexIso F I.cocomplex ComplexShape.embeddingUpNat).hom ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom := rfl

/-- The objectwise comparison of the original ordinary right derived functor
with the bounded below derived functor, computed using the same resolution. -/
def rightDerivedPlusComparisonObjIso {A : C} (I : InjectiveResolution A) (n : ℕ) :
    (F.rightDerived n).obj A ≅
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A)) :=
  I.isoRightDerivedObj F n ≪≫ (mappedResolutionPlusHomologyIso F I n).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
      (rightDerivedPlusResolutionIso F I)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality uses the same resolution morphism on both sides of the comparison. -/
theorem rightDerivedPlusComparisonObjIso_naturality {A B : C}
    {I : InjectiveResolution A} {J : InjectiveResolution B} {f : A ⟶ B}
    (φ : I.Hom J f) (n : ℕ) :
    (F.rightDerived n).map f ≫ (rightDerivedPlusComparisonObjIso F J n).hom =
      (rightDerivedPlusComparisonObjIso F I n).hom ≫
        (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) := by
  have h₁ := I.isoRightDerivedObj_hom_naturality f J φ.hom
    (by simp) F n
  have h₂ := (mappedNonnegativeComplexHomologyIso F n).inv.naturality φ.hom
  have h₃ := (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).congr_map
    (rightDerivedPlusResolutionIso_naturality F φ)
  simp only [Functor.map_comp] at h₃
  simp only [rightDerivedPlusComparisonObjIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, mappedResolutionPlusHomologyIso, Iso.app_inv, assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordinary right derived functor is naturally the homology of
the bounded below derived functor on objects in degree zero. -/
def rightDerivedPlusComparisonIso (n : ℕ) :
    F.rightDerived n ≅
      DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D (n : ℤ) :=
  NatIso.ofComponents (fun A => rightDerivedPlusComparisonObjIso F (injectiveResolution A) n)
    (fun f => rightDerivedPlusComparisonObjIso_naturality F
      ⟨InjectiveResolution.desc f _ _, by
        rw [CochainComplex.single₀_map_f_zero]
        exact InjectiveResolution.desc_commutes_zero f _ _⟩ n)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical identification of the source of the degree-zero RF-plus unit
with `F.obj A`, using the actual mapped single complex. -/
def rightDerivedPlusUnitSourceIso (A : C) :
    (DerivedCategory.Plus.homologyFunctor D 0).obj
        (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (singleZeroCochainPlus A))) ≅
      F.obj A :=
  (cochainPlusHomologyFunctorIso (C := D) 0).app
      (F.mapCochainComplexPlus.obj (singleZeroCochainPlus A)) ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app A) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj A)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero map comes directly from the original RF-plus unit. -/
def rightDerivedPlusZeroUnit (A : C) :
    F.obj A ⟶
      (DerivedCategory.Plus.homologyFunctor D 0).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A)) :=
  (rightDerivedPlusUnitSourceIso F A).inv ≫
    (DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))

omit [EnoughInjectives C] [HasDerivedCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Computing degree-zero homology of the actual augmentation recovers the
original map from `F.obj A` to the resolution cycles. -/
theorem mappedResolutionPlusHomologyIso_augmentation_zero {A : C}
    (I : InjectiveResolution A) :
    (rightDerivedPlusUnitSourceIso F A).inv ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (DerivedCategory.Plus.Q.map
            (F.mapCochainComplexPlus.map (injectiveResolutionPlusAugmentation I))) ≫
        (mappedResolutionPlusHomologyIso F I 0).hom =
      I.toRightDerivedZero' F ≫
        (CochainComplex.isoHomologyπ₀
          ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).hom := by
  let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let g : (HomologicalComplex.single D (.up ℤ) 0).obj (F.obj A) ⟶
      K.extend ComplexShape.embeddingUpNat :=
    (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app A) ≫
      (F.mapHomologicalComplex (.up ℤ)).map I.ι') ≫
        (mapExtendComplexIso F I.cocomplex ComplexShape.embeddingUpNat).hom
  have hu : I.toRightDerivedZero' F ≫ K.iCycles 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj A)).inv ≫ g.f 0 ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom := by
    dsimp only [g, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    simp only [assoc]
    rw [mapExtendComplexIso_hom_f_comp,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [assoc, Iso.inv_hom_id_assoc]
    rw [InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      ← Functor.map_comp_assoc, ← Functor.map_comp]
    apply F.congr_map
    simp [InjectiveResolution.ι'_f_zero, InjectiveResolution.cochainComplexXIso, assoc]
  have hg := singleToExtendedHomology_zero K g (I.toRightDerivedZero' F) hu
  have hc := (cochainPlusHomologyFunctorIso (C := D) 0).hom.naturality
    (F.mapCochainComplexPlus.map (injectiveResolutionPlusAugmentation I))
  rw [mappedResolutionPlusHomologyIso_hom]
  simp only [rightDerivedPlusUnitSourceIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.app_inv, Int.natCast_zero, assoc]
  rw [reassoc_of% hc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  exact hg

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Under the comparison using the same `I`, the RF-plus unit is exactly
the existing `toRightDerivedZero` map. -/
theorem rightDerivedPlusComparisonObjIso_zero_unit {A : C} (I : InjectiveResolution A) :
    F.toRightDerivedZero.app A ≫ (rightDerivedPlusComparisonObjIso F I 0).hom =
      rightDerivedPlusZeroUnit F A := by
  rw [I.toRightDerivedZero_eq F]
  simp only [rightDerivedPlusComparisonObjIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Int.natCast_zero, assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% (mappedResolutionPlusHomologyIso_augmentation_zero F I)]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, rightDerivedPlusResolutionIso_augmentation]
  rfl

/-- The natural comparison carries the original degree-zero map to the actual
RF-plus unit, with its canonical source identification. -/
theorem rightDerivedPlusComparisonIso_zero_unit (A : C) :
    F.toRightDerivedZero.app A ≫ (rightDerivedPlusComparisonIso F 0).hom.app A =
      rightDerivedPlusZeroUnit F A :=
  rightDerivedPlusComparisonObjIso_zero_unit F (injectiveResolution A)

end Derived

#print axioms mapExtendComplexXIso
#print axioms mapExtendComplexIso
#print axioms mapExtendComplexIso_naturality
#print axioms mapExtendFunctorIso
#print axioms mapExtendComplexIso_hom_f_comp
#print axioms extendHomologyFunctorIso
#print axioms mapCochainPlusQuotient_map
#print axioms singleToExtendedHomology_zero
#print axioms nonnegativeCochainPlus
#print axioms injectiveResolutionCochainPlus
#print axioms singleZeroCochainPlus
#print axioms injectiveResolutionPlusAugmentation
#print axioms injectiveResolutionDerivedPlusIso
#print axioms injectiveResolutionDerivedPlusIso_hom
#print axioms injectiveResolutionDerivedPlusIso_naturality
#print axioms cochainPlusHomologyFunctorIso
#print axioms rightDerivedPlusResolutionIso
#print axioms rightDerivedPlusResolutionIso_naturality
#print axioms rightDerivedPlusResolutionIso_augmentation
#print axioms mappedNonnegativeComplexHomologyIso
#print axioms mappedResolutionPlusHomologyIso
#print axioms mappedResolutionPlusHomologyIso_hom
#print axioms rightDerivedPlusComparisonObjIso
#print axioms rightDerivedPlusComparisonObjIso_naturality
#print axioms rightDerivedPlusComparisonIso
#print axioms rightDerivedPlusUnitSourceIso
#print axioms rightDerivedPlusZeroUnit
#print axioms mappedResolutionPlusHomologyIso_augmentation_zero
#print axioms rightDerivedPlusComparisonObjIso_zero_unit
#print axioms rightDerivedPlusComparisonIso_zero_unit

end PrimeGap182.TypeIII
