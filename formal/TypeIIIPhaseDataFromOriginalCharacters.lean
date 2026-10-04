import TypeIIIOriginPoleWildFromOriginalParameter
import Mathlib.Algebra.DirectSum.Module

/-!
# Phase data from the ORIGINAL parameter/J characters

Phases are defined as nonzero categorical Hom support from the actual
ORIGINAL AS(beta/t) characters, including coefficient0. A profile means
an actual finite direct-sum decomposition into those same characters.
Mathlib direct-sum projections/inclusions prove exact support detection;
general AS rank-one, separation and coefficient-zero triviality are
explicit character premises. No tensor/dual/subquotient PhaseRules, wild
stalk construction, all-representation decomposition or Type III phase
exclusion is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters
open PublishedPhaseApplication OriginPoleWildFromOriginalParameter

universe u v w mu
variable {E : Type v} [Field E] {G : Type w} [Group G]

/-- Categorical morphism with the specified equivariant linear map. -/
def repHom {R S : FDRep E G} (f : Representation.IntertwiningMap R.ρ S.ρ) : R ⟶ S :=
  FDRep.forget₂HomLinearEquiv R S (Rep.ofHom f)

/-- Read the actual equivariant morphism's underlying linear map. -/
def underlying {R S : FDRep E G} (f : R ⟶ S) : R →ₗ[E] S := f.hom.hom.hom

@[simp] theorem underlying_repHom {R S : FDRep E G}
    (f : Representation.IntertwiningMap R.ρ S.ρ) :
    underlying (repHom f) = f.toLinearMap := rfl

@[simp] theorem underlying_zero {R S : FDRep E G} :
    underlying (0 : R ⟶ S) = 0 := rfl

@[simp] theorem underlying_id (R : FDRep E G) :
    underlying (𝟙 R) = LinearMap.id := rfl

@[simp] theorem underlying_comp {R S T : FDRep E G} (f : R ⟶ S) (g : S ⟶ T) :
    underlying (f ≫ g) = (underlying g).comp (underlying f) := rfl

/-- Faithfulness is inherited from actual action/module morphisms. -/
theorem hom_ext {R S : FDRep E G} {f g : R ⟶ S}
    (h : underlying f = underlying g) : f = g := by
  apply Action.hom_ext
  apply InducedCategory.hom_ext
  exact ModuleCat.hom_ext h

/-- The equivariant projection onto one summand of the actual direct sum. -/
def sumProjection {ι : Type} [Fintype ι] (R : ι → FDRep E G) (i : ι) :
    finiteSum R ⟶ R i :=
  repHom {
    toLinearMap := DirectSum.component E ι (fun j => (R j).V) i
    isIntertwining' g := by
      ext x
      rfl
  }

/-- The equivariant inclusion of one summand into the actual direct sum. -/
def sumInclusion {ι : Type} [Fintype ι] (R : ι → FDRep E G) (i : ι) :
    R i ⟶ finiteSum R :=
  repHom {
    toLinearMap := DirectSum.lof E ι (fun j => (R j).V) i
    isIntertwining' g := by
      ext x
      exact (DirectSum.lmap_lof (fun j => (R j).ρ g) i x).symm
  }

theorem inclusion_projection {ι : Type} [Fintype ι] (R : ι → FDRep E G) (i : ι) :
    sumInclusion R i ≫ sumProjection R i = 𝟙 (R i) := by
  apply hom_ext
  change DirectSum.component E ι (fun j => (R j).V) i ∘ₗ
    DirectSum.lof E ι (fun j => (R j).V) i = LinearMap.id
  exact DirectSum.component_comp_lof_same E i

/-- A map into the finite direct sum vanishes exactly when every
component vanishes. The statement includes the empty index type. -/
theorem map_to_sum_eq_zero_iff {ι : Type} [Fintype ι] {X : FDRep E G}
    (R : ι → FDRep E G) (f : X ⟶ finiteSum R) :
    f = 0 ↔ ∀ i, f ≫ sumProjection R i = 0 := by
  constructor
  · intro h i
    simp [h]
  · intro h
    apply hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    have hi := congrArg (fun q => underlying q x) (h i)
    simp only [underlying_comp, sumProjection, underlying_repHom, underlying_zero,
      LinearMap.comp_apply, LinearMap.zero_apply] at hi
    simp only [underlying_zero, LinearMap.zero_apply, DFinsupp.zero_apply]
    with_unfolding_all exact hi

/-- Exact nonzero-Hom support detection for the actual finite sum. -/
theorem homWitness_finiteSum_iff {ι : Type} [Fintype ι] (R : ι → FDRep E G)
    (X : FDRep E G) :
    (∃ f : X ⟶ finiteSum R, f ≠ 0) ↔ ∃ i, ∃ f : X ⟶ R i, f ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    have h : ¬ ∀ i, f ≫ sumProjection R i = 0 := by
      intro he
      exact hf ((map_to_sum_eq_zero_iff R f).mpr he)
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact ⟨i, f ≫ sumProjection R i, hi⟩
  · rintro ⟨i, f, hf⟩
    refine ⟨f ≫ sumInclusion R i, ?_⟩
    intro h
    apply hf
    have hc := congrArg (fun q => q ≫ sumProjection R i) h
    simpa only [Category.assoc, inclusion_projection, Category.comp_id, zero_comp] using hc

/-- Isomorphism of the target preserves nonzero Hom witnesses. -/
theorem homWitness_isoRight {C : Type*} [Category C] [HasZeroMorphisms C]
    {X R S : C} (e : R ≅ S) :
    (∃ f : X ⟶ R, f ≠ 0) ↔ ∃ f : X ⟶ S, f ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f ≫ e.hom, ?_⟩
    intro h
    apply hf
    have hc := congrArg (fun q => q ≫ e.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] using hc
  · rintro ⟨f, hf⟩
    refine ⟨f ≫ e.inv, ?_⟩
    intro h
    apply hf
    have hc := congrArg (fun q => q ≫ e.hom) h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hc

/-- Canonical comparison with the one-summand actual direct sum. -/
def singletonSumIso {ι : Type} [Fintype ι] [Unique ι] (R : FDRep E G) :
    R ≅ finiteSum (fun _ : ι => R) where
  hom := sumInclusion (fun _ : ι => R) default
  inv := sumProjection (fun _ : ι => R) default
  hom_inv_id := inclusion_projection _ _
  inv_hom_id := by
    let : DecidableEq ι := fun a b => Classical.propDecidable (a = b)
    apply hom_ext
    apply LinearMap.ext
    intro x
    apply DirectSum.ext_component E
    intro i
    have hi : i = default := Subsingleton.elim _ _
    subst i
    simp only [underlying_comp, sumProjection, sumInclusion, underlying_repHom,
      LinearMap.comp_apply, underlying_id, LinearMap.id_apply]
    with_unfolding_all exact DirectSum.component.lof_self E _ _

variable {K : Type u} [Field K]

/-- Nonzero Hom support from the SAME supplied character family. -/
def homSupport (chi : PhaseField K → FDRep E G) (R : FDRep E G) : Set (PhaseField K) :=
  {beta | ∃ f : chi beta ⟶ R, f ≠ 0}

/-- A profile is a finite direct-sum decomposition, not an arbitrary label. -/
def FiniteCharacterProfile (chi : PhaseField K → FDRep E G) (R : FDRep E G) : Prop :=
  ∃ n : ℕ, ∃ beta : Fin n → PhaseField K,
    Nonempty (R ≅ finiteSum (fun i => chi (beta i)))

/-- PhaseData with no freely supplied observable or membership law. -/
def characterPhaseData (chi : PhaseField K → FDRep E G) : PhaseData K E G where
  HasProfile := FiniteCharacterProfile chi
  phases := homSupport chi

/-- Precise general AS character premises on this same family. Rank and
separation are all-coefficient statements. At coefficient0 the character
is trivial of rank1, never a zero representation. -/
structure CharacterLaws (chi : PhaseField K → FDRep E G) : Prop where
  rank_one : ∀ beta, Module.finrank E (chi beta) = 1
  separated : ∀ beta gamma, beta ≠ gamma → ∀ f : chi beta ⟶ chi gamma, f = 0
  zero_trivial : Representation.IsTrivial (chi 0).ρ

variable {chi : PhaseField K → FDRep E G}

/-- Positive dimension makes the identity an actual nonzero morphism. -/
theorem id_ne_zero_of_rank_one (R : FDRep E G) (hR : Module.finrank E R = 1) :
    (𝟙 R : R ⟶ R) ≠ 0 := by
  intro h
  have hz : Module.finrank E R = 0 :=
    (finrank_zero_iff_forall_zero).mpr (by
      intro x
      exact congrArg (fun q => underlying q x) h)
  omega

/-- Separated rank-one characters have exactly singleton Hom support. -/
theorem CharacterLaws.character_support (L : CharacterLaws chi) (gamma : PhaseField K) :
    homSupport chi (chi gamma) = {gamma} := by
  ext beta
  constructor
  · rintro ⟨f, hf⟩
    by_contra h
    exact hf (L.separated beta gamma h f)
  · intro h
    have he : beta = gamma := h
    subst beta
    exact ⟨𝟙 (chi gamma), id_ne_zero_of_rank_one _ (L.rank_one gamma)⟩

/-- Exact support of a finite sum is the range of its coefficients;
repeated coefficients and coefficient0 are retained. -/
theorem CharacterLaws.finiteSum_support (L : CharacterLaws chi) {ι : Type} [Fintype ι]
    (beta : ι → PhaseField K) :
    homSupport chi (finiteSum (fun i => chi (beta i))) = Set.range beta := by
  ext gamma
  rw [homSupport, Set.mem_ofPred_eq, homWitness_finiteSum_iff]
  constructor
  · rintro ⟨i, hi⟩
    have he : gamma = beta i := by
      have hm : gamma ∈ homSupport chi (chi (beta i)) := hi
      rw [L.character_support] at hm
      exact hm
    exact ⟨i, he.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, 𝟙 (chi (beta i)), id_ne_zero_of_rank_one _ (L.rank_one _)⟩

/-- Every character has the defined finite profile, via a one-summand
isomorphism rather than an assumed profile flag. -/
theorem character_profile (gamma : PhaseField K) : FiniteCharacterProfile chi (chi gamma) :=
  ⟨1, fun _ => gamma, ⟨singletonSumIso (ι := Fin 1) (chi gamma)⟩⟩

/-- The defined phases are invariant under actual target isomorphisms. -/
theorem homSupport_iso {R S : FDRep E G} (e : R ≅ S) :
    homSupport chi R = homSupport chi S := by
  ext beta
  exact homWitness_isoRight e

/-- A finite character decomposition proves finite phase support. -/
theorem CharacterLaws.profile_support_finite (L : CharacterLaws chi) {R : FDRep E G}
    (hR : FiniteCharacterProfile chi R) : (homSupport chi R).Finite := by
  obtain ⟨n, beta, ⟨e⟩⟩ := hR
  rw [homSupport_iso e, L.finiteSum_support]
  exact Set.finite_range beta

/-- The empty decomposition has empty support, by actual map detection. -/
theorem emptySum_support :
    homSupport chi (finiteSum (fun i : Fin 0 => chi (Fin.elim0 i))) = ∅ := by
  ext beta
  simp only [homSupport, Set.mem_ofPred_eq, homWitness_finiteSum_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, _⟩
  exact Fin.elim0 i

/-- The original B parameter/J family, with exact original AS source. -/
def canonicalPD {K0 : Type} [Field K0]
    (B : SourceInverseImageSystem.System.{0,mu} K0)
    (J : B.Obj .parameter ⥤ FDRep E G) (as : B.Obj .line) : PhaseData K0 E G :=
  characterPhaseData (oldCharacter (J := J) as)

/-- Original general recognition is definitional for canonicalPD;
no new all-profiled dictionary law is an input. -/
theorem canonicalRecognition {K0 : Type} [Field K0]
    (B : SourceInverseImageSystem.System.{0,mu} K0)
    (J : B.Obj .parameter ⥤ FDRep E G) (as : B.Obj .line) :
    OriginalASRecognition (J := J) as (canonicalPD B J as) where
  membership _ _ _ := Iff.rfl

/-- Construct the original primitive radial PhaseLaws from general
rank/separation and the canonical finite-decomposition definitions. -/
theorem canonicalPhaseLaws {K0 : Type} [Field K0]
    (B : SourceInverseImageSystem.System.{0,mu} K0)
    (J : B.Obj .parameter ⥤ FDRep E G) (as : B.Obj .line)
    (L : CharacterLaws (oldCharacter (J := J) as)) :
    PrimitiveRadialAS.PhaseLaws K0 (canonicalPD B J as)
      (PrimitiveRadialFromParameter.parameterRestriction B) J as where
  profile := character_profile
  rank := L.rank_one
  phases := L.character_support

end PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters

#print axioms PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters.homWitness_finiteSum_iff
#print axioms PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters.CharacterLaws.character_support
#print axioms PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters.CharacterLaws.profile_support_finite
#print axioms PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters.canonicalRecognition
#print axioms PrimeGap182.TypeIII.PhaseDataFromOriginalCharacters.canonicalPhaseLaws
