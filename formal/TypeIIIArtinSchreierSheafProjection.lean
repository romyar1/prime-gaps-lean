import TypeIIIArtinSchreierSheaf
import Mathlib.CategoryTheory.Retract

/-!
# The global character projection of the Artin--Schreier cover

The actual deck maps satisfy the translation group law on the free
representable presheaf. Reindexing their finite character average proves
idempotence when p is nonzero in the coefficient field. Sheafification
preserves this identity, so the actual character image sheaf is a retract
of the ambient free sheaf through the canonical image factorization.

These arguments use the cover maps and finite averaging directly. They
do not assume any geometric-stalk, rank, or comparison statement.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

/-- The actual module sheafification functor preserves coefficient scalars.
This follows from its adjunction unit and the linear inclusion of sheaves. -/
theorem etaleModuleSheafification_linear (R E : Type u) [CommRing R] [CommRing E] :
    Functor.Linear E
      (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)) := by
  constructor
  intro P Q g r
  apply ((sheafificationAdjunction (Spec (.of R)).smallEtaleTopology
    (ModuleCat.{u} E)).homEquiv P _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_smul]
  change toSheafify (Spec (.of R)).smallEtaleTopology P ≫
      sheafifyMap (Spec (.of R)).smallEtaleTopology (r • g) =
    toSheafify (Spec (.of R)).smallEtaleTopology P ≫
      (r • sheafifyMap (Spec (.of R)).smallEtaleTopology g)
  rw [← toSheafify_naturality, CategoryTheory.Linear.smul_comp,
    CategoryTheory.Linear.comp_smul, ← toSheafify_naturality]

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R)

section RingCoefficients

variable (E : Type u) [CommRing E]

set_option backward.isDefEq.respectTransparency.types false in
/-- The free presheaf map of the identity cover map is the identity. -/
@[simp] theorem artinSchreierFreePresheafMap_id :
    artinSchreierFreePresheafMap p f E (𝟙 (artinSchreierEtaleObject p f)) =
      𝟙 (artinSchreierFreePresheaf p f E) := by
  change Functor.whiskerRight ((shrinkYoneda.{u}).map (𝟙 (artinSchreierEtaleObject p f)))
      (ModuleCat.free E) =
    𝟙 ((shrinkYoneda.{u}).obj (artinSchreierEtaleObject p f) ⋙ ModuleCat.free E)
  rw [(shrinkYoneda.{u}).map_id, Functor.whiskerRight_id']

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual free presheaf construction preserves composition of cover maps. -/
theorem artinSchreierFreePresheafMap_comp
    (g h : artinSchreierEtaleObject p f ⟶ artinSchreierEtaleObject p f) :
    artinSchreierFreePresheafMap p f E g ≫ artinSchreierFreePresheafMap p f E h =
      artinSchreierFreePresheafMap p f E (g ≫ h) := by
  change Functor.whiskerRight ((shrinkYoneda.{u}).map g) (ModuleCat.free E) ≫
      Functor.whiskerRight ((shrinkYoneda.{u}).map h) (ModuleCat.free E) =
    Functor.whiskerRight ((shrinkYoneda.{u}).map (g ≫ h)) (ModuleCat.free E)
  rw [(shrinkYoneda.{u}).map_comp, Functor.whiskerRight_comp]

/-- Actual deck maps act additively on the free representable presheaf. -/
theorem artinSchreierFreePresheafMap_deck_add (a b : ZMod p) :
    artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a) ≫
        artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f b) =
      artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f (a + b)) := by
  rw [artinSchreierFreePresheafMap_comp, artinSchreierEtaleDeck_add]

end RingCoefficients

variable (E : Type u) [Field E]

variable (ψ : AddChar (ZMod p) E)

/-- A deck map after the positive-weight character average has scalar
ψ(-b). This is a finite reindexing of actual presheaf maps. -/
theorem artinSchreierCharacterPresheafAverage_comp_deck (b : ZMod p) :
    artinSchreierCharacterPresheafAverage p f E ψ ≫
        artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f b) =
      ψ (-b) • artinSchreierCharacterPresheafAverage p f E ψ := by
  have hsum :
      (∑ a : ZMod p, ψ a • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f (a + b))) =
      ψ (-b) • ∑ a : ZMod p, ψ a • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f a) := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addRight b) _ _ ?_
    intro a
    change ψ a • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f (a + b)) =
      ψ (-b) • (ψ (a + b) • artinSchreierFreePresheafMap p f E
        (artinSchreierEtaleDeck p f (a + b)))
    have hψ : ψ (-b) * ψ (a + b) = ψ a := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      abel
    rw [smul_smul, hψ]
  simp only [artinSchreierCharacterPresheafAverage,
    CategoryTheory.Linear.smul_comp, Preadditive.sum_comp,
    artinSchreierFreePresheafMap_deck_add]
  rw [hsum, smul_comm]

/-- The deck action commutes with the actual character presheaf average. -/
theorem artinSchreierCharacterPresheafAverage_deck_commute (b : ZMod p) :
    artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f b) ≫
        artinSchreierCharacterPresheafAverage p f E ψ =
      artinSchreierCharacterPresheafAverage p f E ψ ≫
        artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f b) := by
  simp only [artinSchreierCharacterPresheafAverage,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum,
    artinSchreierFreePresheafMap_deck_add]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [add_comm a b]

/-- Applying the character average twice is the same as applying it once.
The normalization is the actual cardinality p of the deck group. -/
theorem artinSchreierCharacterPresheafAverage_idempotent (hpE : (p : E) ≠ 0) :
    artinSchreierCharacterPresheafAverage p f E ψ ≫
        artinSchreierCharacterPresheafAverage p f E ψ =
      artinSchreierCharacterPresheafAverage p f E ψ := by
  change artinSchreierCharacterPresheafAverage p f E ψ ≫
      ((p : E)⁻¹ • ∑ a : ZMod p, ψ a •
        artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a)) = _
  simp only [CategoryTheory.Linear.comp_smul, Preadditive.comp_sum,
    artinSchreierCharacterPresheafAverage_comp_deck, smul_smul,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_smul,
    Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hpE, one_smul]

/-- Sheafification preserves the proved idempotence of the actual average. -/
theorem artinSchreierCharacterSheafAverage_idempotent (hpE : (p : E) ≠ 0) :
    artinSchreierCharacterSheafAverage p f E ψ ≫
        artinSchreierCharacterSheafAverage p f E ψ =
      artinSchreierCharacterSheafAverage p f E ψ := by
  change (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
      (artinSchreierCharacterPresheafAverage p f E ψ) ≫
      (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
        (artinSchreierCharacterPresheafAverage p f E ψ) = _
  rw [← Functor.map_comp, artinSchreierCharacterPresheafAverage_idempotent p f E ψ hpE]
  rfl

/-- The actual sheaf deck map after the average has the negative character scalar. -/
theorem artinSchreierCharacterSheafAverage_comp_deck (a : ZMod p) :
    artinSchreierCharacterSheafAverage p f E ψ ≫
        artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a) =
      ψ (-a) • artinSchreierCharacterSheafAverage p f E ψ := by
  let := etaleModuleSheafification_linear R E
  change (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
      (artinSchreierCharacterPresheafAverage p f E ψ) ≫
      (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
        (artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a)) =
    ψ (-a) • (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
      (artinSchreierCharacterPresheafAverage p f E ψ)
  rw [← Functor.map_comp, artinSchreierCharacterPresheafAverage_comp_deck, Functor.map_smul]

/-- Actual sheaf deck maps commute with the actual character average. -/
theorem artinSchreierCharacterSheafAverage_deck_commute (a : ZMod p) :
    artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a) ≫
        artinSchreierCharacterSheafAverage p f E ψ =
      artinSchreierCharacterSheafAverage p f E ψ ≫
        artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a) := by
  change (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
      (artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a)) ≫
      (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
        (artinSchreierCharacterPresheafAverage p f E ψ) =
    (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
      (artinSchreierCharacterPresheafAverage p f E ψ) ≫
      (presheafToSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)).map
        (artinSchreierFreePresheafMap p f E (artinSchreierEtaleDeck p f a))
  rw [← Functor.map_comp, artinSchreierCharacterPresheafAverage_deck_commute, Functor.map_comp]

/-- The canonical factorization of the actual sheaf average through its image. -/
def artinSchreierCharacterSheafRetraction :
    artinSchreierFreeSheaf p f E ⟶ artinSchreierCharacterImageSheaf p f E ψ :=
  Abelian.factorThruImage (artinSchreierCharacterSheafAverage p f E ψ)

/-- Retraction followed by the literal image inclusion is the actual average. -/
theorem artinSchreierCharacterSheafRetraction_comp_inclusion :
    artinSchreierCharacterSheafRetraction p f E ψ ≫
        Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) =
      artinSchreierCharacterSheafAverage p f E ψ :=
  Abelian.image.fac _

/-- The actual image inclusion is split by the canonical image factorization. -/
theorem artinSchreierCharacterSheafInclusion_comp_retraction (hpE : (p : E) ≠ 0) :
    Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) ≫
        artinSchreierCharacterSheafRetraction p f E ψ =
      𝟙 (artinSchreierCharacterImageSheaf p f E ψ) := by
  let P := artinSchreierCharacterSheafAverage p f E ψ
  change Abelian.image.ι P ≫ Abelian.factorThruImage P = 𝟙 _
  apply (cancel_epi (Abelian.factorThruImage P)).mp
  apply (cancel_mono (Abelian.image.ι P)).mp
  calc
    (Abelian.factorThruImage P ≫
        (Abelian.image.ι P ≫ Abelian.factorThruImage P)) ≫ Abelian.image.ι P =
        (Abelian.factorThruImage P ≫ Abelian.image.ι P) ≫
          (Abelian.factorThruImage P ≫ Abelian.image.ι P) := by
      simp only [Category.assoc]
    _ = P ≫ P := by rw [Abelian.image.fac]
    _ = P := artinSchreierCharacterSheafAverage_idempotent p f E ψ hpE
    _ = (Abelian.factorThruImage P ≫ 𝟙 _) ≫ Abelian.image.ι P := by
      rw [Category.comp_id, Abelian.image.fac]

/-- The existing character image sheaf is an actual retract of the ambient
free sheaf, with the canonical inclusion and factorization as its maps. -/
def artinSchreierCharacterImageSheafRetract (hpE : (p : E) ≠ 0) :
    Retract (artinSchreierCharacterImageSheaf p f E ψ)
      (artinSchreierFreeSheaf p f E) where
  i := Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ)
  r := artinSchreierCharacterSheafRetraction p f E ψ
  retract := artinSchreierCharacterSheafInclusion_comp_retraction p f E ψ hpE

/-- The average acts as the identity after the actual image inclusion. -/
theorem artinSchreierCharacterSheafInclusion_comp_average (hpE : (p : E) ≠ 0) :
    Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) ≫
        artinSchreierCharacterSheafAverage p f E ψ =
      Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) := by
  let P := artinSchreierCharacterSheafAverage p f E ψ
  have hfix : Abelian.image.ι P ≫ Abelian.factorThruImage P = 𝟙 _ :=
    artinSchreierCharacterSheafInclusion_comp_retraction p f E ψ hpE
  change Abelian.image.ι P ≫ P = Abelian.image.ι P
  calc
    _ = Abelian.image.ι P ≫ (Abelian.factorThruImage P ≫ Abelian.image.ι P) :=
      congrArg (fun g => Abelian.image.ι P ≫ g) (Abelian.image.fac P).symm
    _ = _ := by
      rw [← Category.assoc, hfix, Category.id_comp]

/-- Restricting the actual ambient deck map to the actual image inclusion
gives the negative character scalar. -/
theorem artinSchreierCharacterSheafInclusion_comp_deck (hpE : (p : E) ≠ 0)
    (a : ZMod p) :
    Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) ≫
        artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a) =
      ψ (-a) • Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) := by
  let P := artinSchreierCharacterSheafAverage p f E ψ
  let D := artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a)
  have hi : Abelian.image.ι P ≫ P = Abelian.image.ι P :=
    artinSchreierCharacterSheafInclusion_comp_average p f E ψ hpE
  have hPD : P ≫ D = ψ (-a) • P :=
    artinSchreierCharacterSheafAverage_comp_deck p f E ψ a
  change Abelian.image.ι P ≫ D = ψ (-a) • Abelian.image.ι P
  calc
    _ = (Abelian.image.ι P ≫ P) ≫ D := congrArg (fun h => h ≫ D) hi.symm
    _ = Abelian.image.ι P ≫ (P ≫ D) := Category.assoc _ _ _
    _ = _ := by rw [hPD, CategoryTheory.Linear.comp_smul, hi]

/-- The actual deck endomorphism on the existing image sheaf, obtained
by inclusion, the actual cover action, and canonical image factorization. -/
def artinSchreierCharacterImageSheafDeck (a : ZMod p) :
    artinSchreierCharacterImageSheaf p f E ψ ⟶
      artinSchreierCharacterImageSheaf p f E ψ :=
  Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) ≫
    artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a) ≫
      artinSchreierCharacterSheafRetraction p f E ψ

/-- The independently constructed image deck map acts by ψ(-a). -/
theorem artinSchreierCharacterImageSheafDeck_eq_smul (hpE : (p : E) ≠ 0)
    (a : ZMod p) :
    artinSchreierCharacterImageSheafDeck p f E ψ a =
      ψ (-a) • 𝟙 (artinSchreierCharacterImageSheaf p f E ψ) := by
  let P := artinSchreierCharacterSheafAverage p f E ψ
  let D := artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a)
  have hiD : Abelian.image.ι P ≫ D = ψ (-a) • Abelian.image.ι P :=
    artinSchreierCharacterSheafInclusion_comp_deck p f E ψ hpE a
  have hir : Abelian.image.ι P ≫ Abelian.factorThruImage P = 𝟙 _ :=
    artinSchreierCharacterSheafInclusion_comp_retraction p f E ψ hpE
  change Abelian.image.ι P ≫ D ≫ Abelian.factorThruImage P = ψ (-a) • 𝟙 (Abelian.image P)
  rw [← Category.assoc, hiD, CategoryTheory.Linear.smul_comp, hir]

/-- The image deck map is the restriction of the actual ambient deck
map, as certified by its commuting square with the literal inclusion. -/
theorem artinSchreierCharacterImageSheafDeck_inclusion (hpE : (p : E) ≠ 0)
    (a : ZMod p) :
    artinSchreierCharacterImageSheafDeck p f E ψ a ≫
        Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) =
      Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) ≫
        artinSchreierFreeSheafMap p f E (artinSchreierEtaleDeck p f a) := by
  rw [artinSchreierCharacterImageSheafDeck_eq_smul p f E ψ hpE a]
  change (ψ (-a) • 𝟙 (Abelian.image (artinSchreierCharacterSheafAverage p f E ψ))) ≫
      Abelian.image.ι (artinSchreierCharacterSheafAverage p f E ψ) = _
  rw [CategoryTheory.Linear.smul_comp, Category.id_comp,
    artinSchreierCharacterSheafInclusion_comp_deck p f E ψ hpE a]

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.etaleModuleSheafification_linear
#print axioms PrimeGap182.TypeIII.artinSchreierFreePresheafMap_id
#print axioms PrimeGap182.TypeIII.artinSchreierFreePresheafMap_comp
#print axioms PrimeGap182.TypeIII.artinSchreierFreePresheafMap_deck_add
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterPresheafAverage_comp_deck
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterPresheafAverage_deck_commute
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterPresheafAverage_idempotent
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage_idempotent
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage_comp_deck
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafAverage_deck_commute
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafRetraction
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafRetraction_comp_inclusion
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafInclusion_comp_retraction
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheafRetract
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafInclusion_comp_average
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterSheafInclusion_comp_deck
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheafDeck
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheafDeck_eq_smul
#print axioms PrimeGap182.TypeIII.artinSchreierCharacterImageSheafDeck_inclusion
