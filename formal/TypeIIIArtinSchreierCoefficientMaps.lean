import TypeIIIArtinSchreierRingSheaf

/-!
# Coefficient maps on the actual Artin--Schreier character sheaves

Changing coefficients sends each generator of the existing free
representable presheaf to the same generator. Sheafification extends
this map to the original free sheaves. Character compatibility then
intertwines the actual averaging projectors, and their proved
splittings induce maps between the original image sheaves.

The construction uses restriction of scalars and its canonical
identity and composition isomorphisms. It does not assume that
extension of scalars preserves images and makes no cohomology claim.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

section CoefficientFunctors

variable {E E' E'' : Type u} [CommRing E] [CommRing E'] [CommRing E'']

/-- Changing coefficients in a free module preserves its actual generators. -/
def freeModuleCoefficientMap (r : E →+* E') :
    ModuleCat.free E ⟶ ModuleCat.free E' ⋙ ModuleCat.restrictScalars r where
  app X := ModuleCat.freeDesc
    (M := (ModuleCat.restrictScalars r).obj ((ModuleCat.free E').obj X))
    (↾fun x => ModuleCat.freeMk (R := E') x)
  naturality {X Y} g := by
    apply ModuleCat.free_hom_ext
    intro x
    simp
    exact (ModuleCat.free_map_apply (R := E') g x).symm

@[simp]
theorem freeModuleCoefficientMap_generator (r : E →+* E') (X : Type u) (x : X) :
    (freeModuleCoefficientMap r).app X (ModuleCat.freeMk x) =
      ModuleCat.freeMk (R := E') x := by
  simp [freeModuleCoefficientMap]
  rfl

/-- Identity coefficient change agrees with the canonical scalar comparison. -/
theorem freeModuleCoefficientMap_id :
    freeModuleCoefficientMap (RingHom.id E) ≫
        Functor.whiskerLeft (ModuleCat.free E) (ModuleCat.restrictScalarsId E).hom =
      𝟙 (ModuleCat.free E) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  intro x
  change (ModuleCat.restrictScalarsId E).hom.app _
      ((freeModuleCoefficientMap (RingHom.id E)).app X (ModuleCat.freeMk x)) =
    ModuleCat.freeMk x
  rw [freeModuleCoefficientMap_generator]
  rfl

/-- Two actual free-module coefficient changes compose canonically. -/
theorem freeModuleCoefficientMap_comp (r : E →+* E') (s : E' →+* E'') :
    freeModuleCoefficientMap r ≫
        Functor.whiskerRight (freeModuleCoefficientMap s) (ModuleCat.restrictScalars r) =
      freeModuleCoefficientMap (s.comp r) ≫
        Functor.whiskerLeft (ModuleCat.free E'') (ModuleCat.restrictScalarsComp r s).hom := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  intro x
  change (ModuleCat.restrictScalars r).map ((freeModuleCoefficientMap s).app X)
      ((freeModuleCoefficientMap r).app X (ModuleCat.freeMk x)) =
    (ModuleCat.restrictScalarsComp r s).hom.app _
      ((freeModuleCoefficientMap (s.comp r)).app X (ModuleCat.freeMk x))
  simp only [freeModuleCoefficientMap_generator]
  exact freeModuleCoefficientMap_generator s X x

/-- Restriction sends multiplication by the image of a scalar to
multiplication by the original scalar. -/
theorem restrictScalars_map_image_smul (r : E →+* E') (c : E)
    {M N : ModuleCat.{u} E'} (g : M ⟶ N) :
    (ModuleCat.restrictScalars r).map (r c • g) =
      c • (ModuleCat.restrictScalars r).map g := by
  ext x
  rfl

/-- A ring map preserves the inverse of the specified natural-number unit. -/
theorem coefficientMap_invOf_natCast (r : E →+* E') (p : ℕ)
    [Invertible (p : E)] [Invertible (p : E')] :
    r (⅟(p : E)) = ⅟(p : E') := by
  symm
  apply invOf_eq_right_inv
  rw [← map_natCast r p, ← map_mul, mul_invOf_self, map_one]

end CoefficientFunctors

section SheafRestriction

variable (R : Type u) [CommRing R]
  {E E' E'' : Type u} [CommRing E] [CommRing E'] [CommRing E'']

/-- Actual restriction of coefficient scalars on the small étale site. -/
abbrev etaleModuleCoefficientRestriction (r : E →+* E') :
    Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E') ⥤
      Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E) :=
  sheafCompose (Spec (.of R)).smallEtaleTopology (ModuleCat.restrictScalars r)

/-- The canonical identity comparison for actual coefficient restriction. -/
def etaleModuleCoefficientRestrictionIdIso :
    etaleModuleCoefficientRestriction R (RingHom.id E) ≅
      𝟭 (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)) :=
  NatIso.ofComponents (fun P =>
    ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj (ModuleCat.restrictScalarsId E)))
    (by intro P Q g; apply Sheaf.hom_ext; ext X x; rfl)

/-- The canonical comparison between composite and successive restrictions. -/
def etaleModuleCoefficientRestrictionCompIso (r : E →+* E') (s : E' →+* E'') :
    etaleModuleCoefficientRestriction R (s.comp r) ≅
      etaleModuleCoefficientRestriction R s ⋙ etaleModuleCoefficientRestriction R r :=
  NatIso.ofComponents (fun P =>
    ObjectProperty.isoMk _
      (Functor.isoWhiskerLeft P.obj (ModuleCat.restrictScalarsComp r s)))
    (by intro P Q g; apply Sheaf.hom_ext; ext X x; rfl)

end SheafRestriction

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R)
  {E E' E'' : Type u} [CommRing E] [CommRing E'] [CommRing E'']

/-- Coefficient change on the existing free representable presheaf. -/
def artinSchreierFreePresheafCoefficientMap (r : E →+* E') :
    artinSchreierFreePresheaf p f E ⟶
      artinSchreierFreePresheaf p f E' ⋙ ModuleCat.restrictScalars r :=
  Functor.whiskerLeft (shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f))
    (freeModuleCoefficientMap r)

/-- Changing coefficients commutes with every actual cover endomorphism. -/
theorem artinSchreierFreePresheafCoefficientMap_deck (r : E →+* E')
    (g : artinSchreierEtaleObject p f ⟶ artinSchreierEtaleObject p f) :
    artinSchreierFreePresheafMap p f E g ≫
        artinSchreierFreePresheafCoefficientMap p f r =
      artinSchreierFreePresheafCoefficientMap p f r ≫
        Functor.whiskerRight (artinSchreierFreePresheafMap p f E' g)
          (ModuleCat.restrictScalars r) := by
  apply NatTrans.ext
  funext X
  exact (freeModuleCoefficientMap r).naturality ((shrinkYoneda.map g).app X)

/-- Identity coefficient change on the existing free presheaf. -/
theorem artinSchreierFreePresheafCoefficientMap_id :
    artinSchreierFreePresheafCoefficientMap p f (RingHom.id E) ≫
        Functor.whiskerLeft (artinSchreierFreePresheaf p f E)
          (ModuleCat.restrictScalarsId E).hom =
      𝟙 (artinSchreierFreePresheaf p f E) := by
  apply NatTrans.ext
  funext X
  exact congrArg (fun η => η.app
    ((shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f)).obj X))
    (freeModuleCoefficientMap_id (E := E))

/-- Composition of actual coefficient changes on the existing free presheaf. -/
theorem artinSchreierFreePresheafCoefficientMap_comp
    (r : E →+* E') (s : E' →+* E'') :
    artinSchreierFreePresheafCoefficientMap p f r ≫
        Functor.whiskerRight (artinSchreierFreePresheafCoefficientMap p f s)
          (ModuleCat.restrictScalars r) =
      artinSchreierFreePresheafCoefficientMap p f (s.comp r) ≫
        Functor.whiskerLeft (artinSchreierFreePresheaf p f E'')
          (ModuleCat.restrictScalarsComp r s).hom := by
  apply NatTrans.ext
  funext X
  exact congrArg (fun η => η.app
    ((shrinkYoneda.{u}.obj (artinSchreierEtaleObject p f)).obj X))
    (freeModuleCoefficientMap_comp r s)

section Averages

variable [Invertible (p : E)] [Invertible (p : E')]
  (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
  (r : E →+* E') (hψ : ∀ a, r (ψ a) = ψ' a)

include hψ

/-- Restricting the target average expresses it with the source scalars. -/
theorem artinSchreierRingCharacterPresheafAverage_restrict :
    Functor.whiskerRight (artinSchreierRingCharacterPresheafAverage p f E' ψ')
        (ModuleCat.restrictScalars r) =
      ⅟(p : E) • ∑ a : ZMod p,
        ψ a • Functor.whiskerRight
          (artinSchreierFreePresheafMap p f E' (artinSchreierEtaleDeck p f a))
          (ModuleCat.restrictScalars r) := by
  apply NatTrans.ext
  funext X
  simp only [Functor.whiskerRight_app, artinSchreierRingCharacterPresheafAverage,
    NatTrans.app_smul, NatTrans.app_sum]
  rw [← coefficientMap_invOf_natCast r p, restrictScalars_map_image_smul,
    Functor.map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← hψ a, restrictScalars_map_image_smul]

/-- The actual source and target character averages intertwine under
coefficient change. -/
theorem artinSchreierRingCharacterPresheafAverage_coefficientMap :
    artinSchreierRingCharacterPresheafAverage p f E ψ ≫
        artinSchreierFreePresheafCoefficientMap p f r =
      artinSchreierFreePresheafCoefficientMap p f r ≫
        Functor.whiskerRight (artinSchreierRingCharacterPresheafAverage p f E' ψ')
          (ModuleCat.restrictScalars r) := by
  rw [artinSchreierRingCharacterPresheafAverage_restrict p f ψ ψ' r hψ]
  simp only [artinSchreierRingCharacterPresheafAverage,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum,
    artinSchreierFreePresheafCoefficientMap_deck]

end Averages

/-- The actual coefficient map extended from the free representable
presheaf through its sheafification universal property. -/
def artinSchreierFreeSheafCoefficientMap (r : E →+* E') :
    artinSchreierFreeSheaf p f E ⟶
      (etaleModuleCoefficientRestriction R r).obj (artinSchreierFreeSheaf p f E') :=
  ⟨sheafifyLift (Spec (.of R)).smallEtaleTopology
    (artinSchreierFreePresheafCoefficientMap p f r ≫
      Functor.whiskerRight
        (toSheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E'))
        (ModuleCat.restrictScalars r))
    ((etaleModuleCoefficientRestriction R r).obj
      (artinSchreierFreeSheaf p f E')).property⟩

/-- The sheaf map is induced by the literal generator coefficient map. -/
theorem artinSchreierFreeSheafCoefficientMap_unit (r : E →+* E') :
    toSheafify (Spec (.of R)).smallEtaleTopology
        (artinSchreierFreePresheaf p f E) ≫
        (artinSchreierFreeSheafCoefficientMap p f r).hom =
      artinSchreierFreePresheafCoefficientMap p f r ≫
        Functor.whiskerRight
          (toSheafify (Spec (.of R)).smallEtaleTopology
            (artinSchreierFreePresheaf p f E'))
          (ModuleCat.restrictScalars r) :=
  toSheafify_sheafifyLift _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Identity coefficient change on the existing free sheaf is the
canonical identity restriction isomorphism. -/
theorem artinSchreierFreeSheafCoefficientMap_id :
    artinSchreierFreeSheafCoefficientMap p f (RingHom.id E) ≫
        (etaleModuleCoefficientRestrictionIdIso R).hom.app
          (artinSchreierFreeSheaf p f E) =
      𝟙 (artinSchreierFreeSheaf p f E) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (artinSchreierFreeSheaf p f E).property
  change toSheafify _ _ ≫
      ((artinSchreierFreeSheafCoefficientMap p f (RingHom.id E)).hom ≫
        Functor.whiskerLeft
          (sheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E))
          (ModuleCat.restrictScalarsId E).hom) =
    toSheafify _ _ ≫ 𝟙 _
  conv_lhs => erw [← Category.assoc, artinSchreierFreeSheafCoefficientMap_unit]
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  intro x
  change (ModuleCat.restrictScalarsId E).hom.app _
      ((ModuleCat.restrictScalars (RingHom.id E)).map
        ((toSheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E)).app X)
        ((freeModuleCoefficientMap (RingHom.id E)).app _ (ModuleCat.freeMk x))) =
    (toSheafify (Spec (.of R)).smallEtaleTopology
      (artinSchreierFreePresheaf p f E)).app X (ModuleCat.freeMk x)
  rw [freeModuleCoefficientMap_generator]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Successive actual free-sheaf coefficient changes equal composite
coefficient change followed by the canonical restriction comparison. -/
theorem artinSchreierFreeSheafCoefficientMap_comp
    (r : E →+* E') (s : E' →+* E'') :
    artinSchreierFreeSheafCoefficientMap p f r ≫
        (etaleModuleCoefficientRestriction R r).map
          (artinSchreierFreeSheafCoefficientMap p f s) =
      artinSchreierFreeSheafCoefficientMap p f (s.comp r) ≫
        (etaleModuleCoefficientRestrictionCompIso R r s).hom.app
          (artinSchreierFreeSheaf p f E'') := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((etaleModuleCoefficientRestriction R r).obj
      ((etaleModuleCoefficientRestriction R s).obj
        (artinSchreierFreeSheaf p f E''))).property
  change toSheafify _ _ ≫
      ((artinSchreierFreeSheafCoefficientMap p f r).hom ≫
        Functor.whiskerRight (artinSchreierFreeSheafCoefficientMap p f s).hom
          (ModuleCat.restrictScalars r)) =
    toSheafify _ _ ≫
      ((artinSchreierFreeSheafCoefficientMap p f (s.comp r)).hom ≫
        Functor.whiskerLeft
          (sheafify (Spec (.of R)).smallEtaleTopology (artinSchreierFreePresheaf p f E''))
          (ModuleCat.restrictScalarsComp r s).hom)
  conv_lhs =>
    erw [← Category.assoc, artinSchreierFreeSheafCoefficientMap_unit,
      Category.assoc, ← Functor.whiskerRight_comp,
      artinSchreierFreeSheafCoefficientMap_unit, Functor.whiskerRight_comp]
  conv_rhs => erw [← Category.assoc, artinSchreierFreeSheafCoefficientMap_unit]
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  intro x
  change (ModuleCat.restrictScalars r).map
      ((ModuleCat.restrictScalars s).map
        ((toSheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E'')).app X))
      ((ModuleCat.restrictScalars r).map ((freeModuleCoefficientMap s).app _)
        ((freeModuleCoefficientMap r).app _ (ModuleCat.freeMk x))) =
    (ModuleCat.restrictScalarsComp r s).hom.app _
      ((ModuleCat.restrictScalars (s.comp r)).map
        ((toSheafify (Spec (.of R)).smallEtaleTopology
          (artinSchreierFreePresheaf p f E'')).app X)
        ((freeModuleCoefficientMap (s.comp r)).app _ (ModuleCat.freeMk x)))
  simp only [freeModuleCoefficientMap_generator]
  change (toSheafify (Spec (.of R)).smallEtaleTopology
      (artinSchreierFreePresheaf p f E'')).app X
      ((freeModuleCoefficientMap s).app _ (ModuleCat.freeMk x)) =
    (toSheafify (Spec (.of R)).smallEtaleTopology
      (artinSchreierFreePresheaf p f E'')).app X (ModuleCat.freeMk x)
  rw [freeModuleCoefficientMap_generator]

section SheafAverages

variable [Invertible (p : E)] [Invertible (p : E')]
  (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
  (r : E →+* E')

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual sheaf averages intertwine under coefficient change. -/
theorem artinSchreierRingCharacterSheafAverage_coefficientMap
    (hψ : ∀ a, r (ψ a) = ψ' a) :
    artinSchreierRingCharacterSheafAverage p f E ψ ≫
        artinSchreierFreeSheafCoefficientMap p f r =
      artinSchreierFreeSheafCoefficientMap p f r ≫
        (etaleModuleCoefficientRestriction R r).map
          (artinSchreierRingCharacterSheafAverage p f E' ψ') := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((etaleModuleCoefficientRestriction R r).obj
      (artinSchreierFreeSheaf p f E')).property
  change toSheafify _ _ ≫
      (sheafifyMap _ (artinSchreierRingCharacterPresheafAverage p f E ψ) ≫
        (artinSchreierFreeSheafCoefficientMap p f r).hom) =
    toSheafify _ _ ≫
      ((artinSchreierFreeSheafCoefficientMap p f r).hom ≫
        Functor.whiskerRight
          (sheafifyMap _ (artinSchreierRingCharacterPresheafAverage p f E' ψ'))
          (ModuleCat.restrictScalars r))
  erw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    artinSchreierFreeSheafCoefficientMap_unit, ← Category.assoc,
    artinSchreierRingCharacterPresheafAverage_coefficientMap p f ψ ψ' r hψ,
    Category.assoc, ← Functor.whiskerRight_comp, toSheafify_naturality,
    Functor.whiskerRight_comp, ← Category.assoc,
    ← artinSchreierFreeSheafCoefficientMap_unit, Category.assoc]

/-- The actual image map is obtained by inclusion, coefficient change,
and the target's canonical split-image retraction. -/
def artinSchreierRingCharacterSheafCoefficientMap :
    artinSchreierRingCharacterImageSheaf p f E ψ ⟶
      (etaleModuleCoefficientRestriction R r).obj
        (artinSchreierRingCharacterImageSheaf p f E' ψ') :=
  Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
    artinSchreierFreeSheafCoefficientMap p f r ≫
      (etaleModuleCoefficientRestriction R r).map
        (artinSchreierRingCharacterSheafRetraction p f E' ψ')

end SheafAverages

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual image inclusion is fixed by the actual projector. -/
theorem artinSchreierRingCharacterSheafInclusion_comp_average
    [Invertible (p : E)] (ψ : AddChar (ZMod p) E) :
    Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
        artinSchreierRingCharacterSheafAverage p f E ψ =
      Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) := by
  calc
    _ = Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
        (artinSchreierRingCharacterSheafRetraction p f E ψ ≫
          Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)) :=
      congrArg (fun g => Abelian.image.ι
        (artinSchreierRingCharacterSheafAverage p f E ψ) ≫ g)
        (artinSchreierRingCharacterSheafRetraction_comp_inclusion p f E ψ).symm
    _ = _ := by
      erw [← Category.assoc,
        artinSchreierRingCharacterSheafInclusion_comp_retraction, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- The induced image map has the actual coefficient map as its
ambient inclusion square. -/
theorem artinSchreierRingCharacterSheafCoefficientMap_inclusion
    [Invertible (p : E)] [Invertible (p : E')]
    (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
    (r : E →+* E') (hψ : ∀ a, r (ψ a) = ψ' a) :
    artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r ≫
        (etaleModuleCoefficientRestriction R r).map
          (Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E' ψ')) =
      Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ) ≫
        artinSchreierFreeSheafCoefficientMap p f r := by
  simp only [artinSchreierRingCharacterSheafCoefficientMap, Category.assoc]
  erw [← Functor.map_comp,
    artinSchreierRingCharacterSheafRetraction_comp_inclusion,
    ← artinSchreierRingCharacterSheafAverage_coefficientMap p f ψ ψ' r hψ,
    ← Category.assoc, artinSchreierRingCharacterSheafInclusion_comp_average]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Identity coefficient change on the actual character image sheaf. -/
theorem artinSchreierRingCharacterSheafCoefficientMap_id
    [Invertible (p : E)] (ψ : AddChar (ZMod p) E) :
    artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ (RingHom.id E) ≫
        (etaleModuleCoefficientRestrictionIdIso R).hom.app
          (artinSchreierRingCharacterImageSheaf p f E ψ) =
      𝟙 (artinSchreierRingCharacterImageSheaf p f E ψ) := by
  let A := artinSchreierRingCharacterImageSheaf p f E ψ
  let A₀ := artinSchreierFreeSheaf p f E
  let F := etaleModuleCoefficientRestriction R (RingHom.id E)
  let iA : A ⟶ A₀ := Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)
  let m : A ⟶ F.obj A :=
    artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ (RingHom.id E)
  let c : A₀ ⟶ F.obj A₀ := artinSchreierFreeSheafCoefficientMap p f (RingHom.id E)
  let e := etaleModuleCoefficientRestrictionIdIso R (E := E)
  have hm : m ≫ F.map iA = iA ≫ c :=
    artinSchreierRingCharacterSheafCoefficientMap_inclusion p f ψ ψ
      (RingHom.id E) (fun _ => rfl)
  have hc : c ≫ e.hom.app A₀ = 𝟙 A₀ := artinSchreierFreeSheafCoefficientMap_id p f
  let : IsSplitMono iA :=
    IsSplitMono.mk'
      ⟨artinSchreierRingCharacterSheafRetraction p f E ψ,
        artinSchreierRingCharacterSheafInclusion_comp_retraction p f E ψ⟩
  apply (cancel_mono iA).mp
  change (m ≫ e.hom.app A) ≫ iA = (𝟙 A) ≫ iA
  calc
    _ = m ≫ (e.hom.app A ≫ iA) := Category.assoc _ _ _
    _ = m ≫ (F.map iA ≫ e.hom.app A₀) :=
      congrArg (fun g => m ≫ g) (e.hom.naturality iA).symm
    _ = (m ≫ F.map iA) ≫ e.hom.app A₀ := (Category.assoc _ _ _).symm
    _ = (iA ≫ c) ≫ e.hom.app A₀ := congrArg (fun g => g ≫ e.hom.app A₀) hm
    _ = iA ≫ (c ≫ e.hom.app A₀) := Category.assoc _ _ _
    _ = iA ≫ 𝟙 A₀ := congrArg (fun g => iA ≫ g) hc
    _ = _ := by rw [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible coefficient changes compose on the original image sheaves,
with the canonical scalar-restriction comparison as coherence map. -/
theorem artinSchreierRingCharacterSheafCoefficientMap_comp
    [Invertible (p : E)] [Invertible (p : E')] [Invertible (p : E'')]
    (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
    (ψ'' : AddChar (ZMod p) E'')
    (r : E →+* E') (s : E' →+* E'')
    (hψr : ∀ a, r (ψ a) = ψ' a) (hψs : ∀ a, s (ψ' a) = ψ'' a) :
    artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r ≫
        (etaleModuleCoefficientRestriction R r).map
          (artinSchreierRingCharacterSheafCoefficientMap p f ψ' ψ'' s) =
      artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ'' (s.comp r) ≫
        (etaleModuleCoefficientRestrictionCompIso R r s).hom.app
          (artinSchreierRingCharacterImageSheaf p f E'' ψ'') := by
  have hψsr (a : ZMod p) : (s.comp r) (ψ a) = ψ'' a := by
    rw [RingHom.comp_apply, hψr, hψs]
  let A := artinSchreierRingCharacterImageSheaf p f E ψ
  let B := artinSchreierRingCharacterImageSheaf p f E' ψ'
  let C := artinSchreierRingCharacterImageSheaf p f E'' ψ''
  let A₀ := artinSchreierFreeSheaf p f E
  let B₀ := artinSchreierFreeSheaf p f E'
  let C₀ := artinSchreierFreeSheaf p f E''
  let F := etaleModuleCoefficientRestriction R r
  let G := etaleModuleCoefficientRestriction R s
  let H := etaleModuleCoefficientRestriction R (s.comp r)
  let iA : A ⟶ A₀ := Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E ψ)
  let iB : B ⟶ B₀ := Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E' ψ')
  let iC : C ⟶ C₀ := Abelian.image.ι (artinSchreierRingCharacterSheafAverage p f E'' ψ'')
  let mr : A ⟶ F.obj B := artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r
  let ms : B ⟶ G.obj C := artinSchreierRingCharacterSheafCoefficientMap p f ψ' ψ'' s
  let mt : A ⟶ H.obj C := artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ'' (s.comp r)
  let cr : A₀ ⟶ F.obj B₀ := artinSchreierFreeSheafCoefficientMap p f r
  let cs : B₀ ⟶ G.obj C₀ := artinSchreierFreeSheafCoefficientMap p f s
  let ct : A₀ ⟶ H.obj C₀ := artinSchreierFreeSheafCoefficientMap p f (s.comp r)
  let e := etaleModuleCoefficientRestrictionCompIso R r s
  have hr : mr ≫ F.map iB = iA ≫ cr :=
    artinSchreierRingCharacterSheafCoefficientMap_inclusion p f ψ ψ' r hψr
  have hs : ms ≫ G.map iC = iB ≫ cs :=
    artinSchreierRingCharacterSheafCoefficientMap_inclusion p f ψ' ψ'' s hψs
  have ht : mt ≫ H.map iC = iA ≫ ct :=
    artinSchreierRingCharacterSheafCoefficientMap_inclusion p f ψ ψ'' (s.comp r) hψsr
  have hc : cr ≫ F.map cs = ct ≫ e.hom.app C₀ :=
    artinSchreierFreeSheafCoefficientMap_comp p f r s
  let : IsSplitMono iC :=
    IsSplitMono.mk'
      ⟨artinSchreierRingCharacterSheafRetraction p f E'' ψ'',
        artinSchreierRingCharacterSheafInclusion_comp_retraction p f E'' ψ''⟩
  apply (cancel_mono (F.map (G.map iC))).mp
  change (mr ≫ F.map ms) ≫ F.map (G.map iC) =
    (mt ≫ e.hom.app C) ≫ F.map (G.map iC)
  calc
    _ = mr ≫ F.map (ms ≫ G.map iC) := by rw [F.map_comp, Category.assoc]
    _ = mr ≫ F.map (iB ≫ cs) := congrArg (fun g => mr ≫ F.map g) hs
    _ = (mr ≫ F.map iB) ≫ F.map cs := by rw [F.map_comp, Category.assoc]
    _ = (iA ≫ cr) ≫ F.map cs := congrArg (fun g => g ≫ F.map cs) hr
    _ = iA ≫ (cr ≫ F.map cs) := Category.assoc _ _ _
    _ = iA ≫ (ct ≫ e.hom.app C₀) := congrArg (fun g => iA ≫ g) hc
    _ = (iA ≫ ct) ≫ e.hom.app C₀ := (Category.assoc _ _ _).symm
    _ = (mt ≫ H.map iC) ≫ e.hom.app C₀ :=
      congrArg (fun g => g ≫ e.hom.app C₀) ht.symm
    _ = mt ≫ (H.map iC ≫ e.hom.app C₀) := Category.assoc _ _ _
    _ = mt ≫ (e.hom.app C ≫ F.map (G.map iC)) :=
      congrArg (fun g => mt ≫ g) (e.hom.naturality iC)
    _ = _ := (Category.assoc _ _ _).symm

#print axioms freeModuleCoefficientMap
#print axioms freeModuleCoefficientMap_generator
#print axioms freeModuleCoefficientMap_id
#print axioms freeModuleCoefficientMap_comp
#print axioms restrictScalars_map_image_smul
#print axioms coefficientMap_invOf_natCast
#print axioms etaleModuleCoefficientRestriction
#print axioms etaleModuleCoefficientRestrictionIdIso
#print axioms etaleModuleCoefficientRestrictionCompIso
#print axioms artinSchreierFreePresheafCoefficientMap
#print axioms artinSchreierFreePresheafCoefficientMap_deck
#print axioms artinSchreierFreePresheafCoefficientMap_id
#print axioms artinSchreierFreePresheafCoefficientMap_comp
#print axioms artinSchreierRingCharacterPresheafAverage_restrict
#print axioms artinSchreierRingCharacterPresheafAverage_coefficientMap
#print axioms artinSchreierFreeSheafCoefficientMap
#print axioms artinSchreierFreeSheafCoefficientMap_unit
#print axioms artinSchreierFreeSheafCoefficientMap_id
#print axioms artinSchreierFreeSheafCoefficientMap_comp
#print axioms artinSchreierRingCharacterSheafAverage_coefficientMap
#print axioms artinSchreierRingCharacterSheafCoefficientMap
#print axioms artinSchreierRingCharacterSheafInclusion_comp_average
#print axioms artinSchreierRingCharacterSheafCoefficientMap_inclusion
#print axioms artinSchreierRingCharacterSheafCoefficientMap_id
#print axioms artinSchreierRingCharacterSheafCoefficientMap_comp

end PrimeGap182.TypeIII
