import TypeIIIPhaseDataFromOriginalCharacters
import TypeIIITensorListRepresentation
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Algebraic phase-rule applications on the SAME separated characters

This module applies actual finite-dimensional representation operations to
canonical finite-character profiles. The only additional published AS
operations are same-family tensor addition and ordinary dual negation.
No universal semisimplicity, observable dictionary or whole PhaseRules
record is an input. The original B/J wild and coefficient realization
remains outside this algebraic application.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Classical BigOperators MonoidAlgebra

namespace PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters
open PublishedPhaseApplication PhaseDataFromOriginalCharacters PublishedMackey TensorListRepresentation
  SelectedTensorTransport OriginPoleWildFromOriginalParameter

universe u v w mu
variable {E : Type v} [Field E] {G : Type w} [Group G]
  {K : Type u} [Field K] {chi : PhaseField K → FDRep E G}

/-- Actual same-family character operations, including coefficient0. -/
structure CharacterOperations (chi : PhaseField K → FDRep E G) where
  tensor : ∀ beta gamma, Representation.Equiv (PublishedMackey.tensor (chi beta) (chi gamma)).ρ
    (chi (beta + gamma)).ρ
  dual : ∀ beta, Representation.Equiv (dualRepresentation (chi beta)).ρ (chi (-beta)).ρ

/-- An equivariant linear equivalence gives an actual FDRep isomorphism. -/
def isoOfEquiv {R S : FDRep E G} (e : Representation.Equiv R.ρ S.ρ) : R ≅ S where
  hom := repHom e.toIntertwiningMap
  inv := repHom e.symm.toIntertwiningMap
  hom_inv_id := by
    apply PhaseDataFromOriginalCharacters.hom_ext
    simp only [underlying_comp, underlying_repHom, underlying_id]
    apply LinearMap.ext
    intro x
    exact e.toLinearEquiv.symm_apply_apply x
  inv_hom_id := by
    apply PhaseDataFromOriginalCharacters.hom_ext
    simp only [underlying_comp, underlying_repHom, underlying_id]
    apply LinearMap.ext
    intro x
    exact e.toLinearEquiv.apply_symm_apply x

/-- Defined profiles transport by composing actual decomposition isomorphisms. -/
theorem profile_iso {R S : FDRep E G} (e : R ≅ S) :
    FiniteCharacterProfile chi R ↔ FiniteCharacterProfile chi S := by
  constructor
  · rintro ⟨n, beta, ⟨h⟩⟩
    exact ⟨n, beta, ⟨e.symm ≪≫ h⟩⟩
  · rintro ⟨n, beta, ⟨h⟩⟩
    exact ⟨n, beta, ⟨e ≪≫ h⟩⟩

/-- Exact original transport field is derived for canonical phase data. -/
theorem transport (R S : FDRep E G) (f : Representation.IntertwiningMap R.ρ S.ρ)
    (hf : Function.Bijective f) :
    ((characterPhaseData chi).HasProfile R ↔ (characterPhaseData chi).HasProfile S) ∧
      (characterPhaseData chi).phases R = (characterPhaseData chi).phases S := by
  let e := isoOfEquiv (f.ofBijective hf)
  exact ⟨profile_iso e, homSupport_iso e⟩

/-- Direct-sum reindexing is equivariant on the actual diagonal action. -/
def sumReindex {ι κ : Type} [Fintype ι] [Fintype κ] (R : ι → FDRep E G) (e : ι ≃ κ) :
    Representation.Equiv (finiteSum R).ρ (finiteSum (fun j => R (e.symm j))).ρ where
  toLinearEquiv := DirectSum.lequivCongrLeft E e
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro j
    change ((DirectSum.lequivCongrLeft E e)
      (DirectSum.lmap (fun i => (R i).ρ g) x)) j =
      (DirectSum.lmap (fun j => (R (e.symm j)).ρ g)
        ((DirectSum.lequivCongrLeft E e) x)) j
    simp only [DirectSum.lequivCongrLeft_apply, DirectSum.lmap_apply]

/-- Any actual finite-indexed character sum has a canonical Fin-indexed profile. -/
theorem finiteSum_profile {ι : Type} [Fintype ι] (beta : ι → PhaseField K) :
    FiniteCharacterProfile chi (finiteSum (fun i => chi (beta i))) :=
  ⟨Fintype.card ι, fun j => beta ((Fintype.equivFin ι).symm j),
    ⟨isoOfEquiv (sumReindex _ (Fintype.equivFin ι))⟩⟩

/-- Flattening nested actual direct sums is equivariant. -/
def sumFlatten {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)]
    (R : (i : ι) → κ i → FDRep E G) :
    Representation.Equiv (finiteSum (fun i => finiteSum (R i))).ρ
      (finiteSum (fun j : Sigma κ => R j.1 j.2)).ρ where
  toLinearEquiv := (DirectSum.sigmaLcurryEquiv E).symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    rintro ⟨i, j⟩
    rfl

/-- Exact original finite-sum profile field, with actual flattening. -/
theorem sum_profile {ι : Type} [Fintype ι] (R : ι → FDRep E G)
    (hR : ∀ i, FiniteCharacterProfile chi (R i)) :
    FiniteCharacterProfile chi (finiteSum R) := by
  choose n beta e using hR
  let V (i : ι) (j : Fin (n i)) := chi (beta i j)
  let h (i : ι) := equivOfIso (e i).some
  let f := (finiteSumEquiv h).trans (sumFlatten V)
  exact (profile_iso (isoOfEquiv f)).mpr (finiteSum_profile (fun j : Sigma (fun i => Fin (n i)) => beta j.1 j.2))

/-- Exact original sum support field, without any profile premise. -/
theorem sum_phases {ι : Type} [Fintype ι] (R : ι → FDRep E G)
    (beta : PhaseField K) (hbeta : beta ∈ homSupport chi (finiteSum R)) :
    ∃ i, beta ∈ homSupport chi (R i) :=
  (homWitness_finiteSum_iff R (chi beta)).mp hbeta

/-- Actual direct-sum inclusions detect maps OUT of the direct sum. -/
theorem map_from_sum_eq_zero_iff {ι : Type} [Fintype ι] (R : ι → FDRep E G)
    {X : FDRep E G} (f : finiteSum R ⟶ X) :
    f = 0 ↔ ∀ i, sumInclusion R i ≫ f = 0 := by
  constructor
  · intro h i
    simp [h]
  · intro h
    apply PhaseDataFromOriginalCharacters.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    have hi := congrArg underlying (h i)
    simp only [underlying_comp, sumInclusion, underlying_repHom, underlying_zero] at hi
    simp only [underlying_zero, LinearMap.zero_comp]
    with_unfolding_all simpa only [LinearMap.zero_comp] using hi

/-- Every nonzero map OUT of a profiled object detects a shared Hom-support
coefficient. No independently supplied phase/naturality rule occurs. -/
theorem nonzero_map_shared_support {R S : FDRep E G}
    (hR : FiniteCharacterProfile chi R) (f : R ⟶ S) (hf : f ≠ 0) :
    ∃ beta, beta ∈ homSupport chi R ∧ beta ∈ homSupport chi S := by
  obtain ⟨n, beta, ⟨e⟩⟩ := hR
  have hcomp : e.inv ≫ f ≠ 0 := by
    intro h
    apply hf
    have he := congrArg (fun q => e.hom ≫ q) h
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, comp_zero] using he
  have h : ¬ ∀ i, sumInclusion (fun j => chi (beta j)) i ≫ e.inv ≫ f = 0 := by
    intro he
    exact hcomp ((map_from_sum_eq_zero_iff _ _).mpr he)
  obtain ⟨i, hi⟩ := not_forall.mp h
  refine ⟨beta i, ?_, ⟨_, hi⟩⟩
  refine ⟨sumInclusion (fun j => chi (beta j)) i ≫ e.inv, ?_⟩
  intro he
  apply hi
  rw [← Category.assoc, he, zero_comp]

/-- Disjoint canonical Hom supports kill every actual morphism from a
profiled object, even when the target has no asserted profile. -/
theorem map_zero_of_disjoint_support {R S : FDRep E G}
    (hR : FiniteCharacterProfile chi R) (h : Disjoint (homSupport chi R) (homSupport chi S))
    (f : R ⟶ S) : f = 0 := by
  by_contra hf
  obtain ⟨beta, hRbeta, hSbeta⟩ := nonzero_map_shared_support hR f hf
  exact Set.disjoint_left.mp h hRbeta hSbeta

/-- A finite sum of actual trivial representations has the trivial action. -/
theorem finiteSum_trivial {ι : Type} [Fintype ι] (R : ι → FDRep E G)
    (hR : ∀ i, Representation.IsTrivial (R i).ρ) :
    Representation.IsTrivial (finiteSum R).ρ := by
  constructor
  intro g
  apply LinearMap.ext
  intro x
  change DirectSum ι (fun i => (R i).V) at x
  apply DFinsupp.ext
  intro i
  change (R i).ρ g (x i) = x i
  exact congrArg (fun f => f (x i)) ((hR i).out g)

/-- Every finite-dimensional trivial representation is an ACTUAL sum of
the SAME rank-one coefficient0 character. No trivial-target dictionary is input. -/
def trivialCharacterEquiv (L : CharacterLaws chi) (R : FDRep E G)
    (hR : Representation.IsTrivial R.ρ) :
    Representation.Equiv R.ρ
      (finiteSum (fun _ : Fin (Module.finrank E R) => chi 0)).ρ where
  toLinearEquiv := LinearEquiv.ofFinrankEq R.V
    (finiteSum (fun _ : Fin (Module.finrank E R) => chi 0)).V (by
    rw [finiteSum_finrank]
    simp only [L.rank_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one])
  isIntertwining' g := by
    rw [hR.out, (finiteSum_trivial _ (fun _ => L.zero_trivial)).out]
    simp only [LinearMap.comp_id, LinearMap.id_comp]

/-- Trivial objects acquire their finite-character profile by construction. -/
theorem trivial_profile (L : CharacterLaws chi) (R : FDRep E G)
    (hR : Representation.IsTrivial R.ρ) : FiniteCharacterProfile chi R :=
  (profile_iso (isoOfEquiv (trivialCharacterEquiv L R hR))).mpr (finiteSum_profile _)

/-- The only possible Hom-support coefficient of a trivial object is0. -/
theorem trivial_support_subset (L : CharacterLaws chi) (R : FDRep E G)
    (hR : Representation.IsTrivial R.ρ) : homSupport chi R ⊆ {0} := by
  rw [homSupport_iso (isoOfEquiv (trivialCharacterEquiv L R hR)), L.finiteSum_support]
  rintro beta ⟨i, rfl⟩
  exact Set.mem_singleton 0

/-- Exact original map-to-trivial field, derived from defined Hom support
and the SAME rank-one trivial character, including arbitrary trivial targets. -/
theorem map_to_trivial_zero (L : CharacterLaws chi) (R S : FDRep E G)
    (hR : FiniteCharacterProfile chi R) (h0 : (0 : PhaseField K) ∉ homSupport chi R)
    (hS : Representation.IsTrivial S.ρ)
    (f : Representation.IntertwiningMap R.ρ S.ρ) : f.toLinearMap = 0 := by
  have hdisjoint : Disjoint (homSupport chi R) (homSupport chi S) := by
    apply Set.disjoint_left.mpr
    intro beta hbeta hSbeta
    have hb : beta = 0 := (trivial_support_subset L S hS hSbeta)
    exact h0 (hb ▸ hbeta)
  have hf := map_zero_of_disjoint_support hR hdisjoint (repHom f)
  have hu := congrArg underlying hf
  simpa only [underlying_repHom, underlying_zero] using hu

/-- Distributivity in BOTH actual finite-sum slots, with the diagonal action. -/
def tensorSumSumEquiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (R : ι → FDRep E G) (S : κ → FDRep E G) :
    Representation.Equiv (tensor (finiteSum R) (finiteSum S)).ρ
      (finiteSum (fun ij : ι × κ => tensor (R ij.1) (S ij.2))).ρ :=
  (Representation.TensorProduct.comm _ _).trans
    ((tensorFiniteSumEquiv (finiteSum S) R).trans
      ((finiteSumEquiv (A := fun i => tensor (finiteSum S) (R i))
        (B := fun i => finiteSum (fun j => tensor (R i) (S j)))
        (fun i => (Representation.TensorProduct.comm _ _).trans
        (tensorFiniteSumEquiv (R i) S))).trans
        ((sumFlatten (fun i j => tensor (R i) (S j))).trans
          (sumReindex _ (Equiv.sigmaEquivProd ι κ)))))

/-- A binary tensor decomposition uses only the SAME-family addition equivalences. -/
theorem tensor_decomposition (C : CharacterOperations chi) {R S : FDRep E G}
    (hR : FiniteCharacterProfile chi R) (hS : FiniteCharacterProfile chi S) :
    ∃ n m, ∃ beta : Fin n → PhaseField K, ∃ gamma : Fin m → PhaseField K,
      Nonempty (R ≅ finiteSum (fun i => chi (beta i))) ∧
      Nonempty (S ≅ finiteSum (fun j => chi (gamma j))) ∧
      Nonempty (tensor R S ≅
        finiteSum (fun ij : Fin n × Fin m => chi (beta ij.1 + gamma ij.2))) := by
  obtain ⟨n, beta, ⟨eR⟩⟩ := hR
  obtain ⟨m, gamma, ⟨eS⟩⟩ := hS
  exact ⟨n, m, beta, gamma, ⟨eR⟩, ⟨eS⟩,
    ⟨isoOfEquiv ((tensorEquiv (equivOfIso eR) (equivOfIso eS)).trans
      ((tensorSumSumEquiv _ _).trans (finiteSumEquiv (fun ij => C.tensor (beta ij.1) (gamma ij.2)))))⟩⟩

/-- Binary tensors of defined profiles acquire a defined finite profile. -/
theorem binary_tensor_profile (C : CharacterOperations chi) {R S : FDRep E G}
    (hR : FiniteCharacterProfile chi R) (hS : FiniteCharacterProfile chi S) :
    FiniteCharacterProfile chi (tensor R S) := by
  obtain ⟨n, m, beta, gamma, _, _, ⟨e⟩⟩ := tensor_decomposition C hR hS
  exact (profile_iso e).mpr (finiteSum_profile _)

/-- Binary tensor Hom support is detected by coefficients in the ORIGINAL factors. -/
theorem binary_tensor_phases (L : CharacterLaws chi) (C : CharacterOperations chi)
    {R S : FDRep E G} (hR : FiniteCharacterProfile chi R) (hS : FiniteCharacterProfile chi S)
    {alpha : PhaseField K} (ha : alpha ∈ homSupport chi (tensor R S)) :
    ∃ beta ∈ homSupport chi R, ∃ gamma ∈ homSupport chi S, alpha = beta + gamma := by
  obtain ⟨n, m, beta, gamma, ⟨eR⟩, ⟨eS⟩, ⟨e⟩⟩ := tensor_decomposition C hR hS
  rw [homSupport_iso e, L.finiteSum_support] at ha
  obtain ⟨ij, hij⟩ := ha
  refine ⟨beta ij.1, ?_, gamma ij.2, ?_, hij.symm⟩
  · rw [homSupport_iso eR, L.finiteSum_support]
    exact Set.mem_range_self ij.1
  · rw [homSupport_iso eS, L.finiteSum_support]
    exact Set.mem_range_self ij.2

/-- Ordinary linear dual/direct-sum distributivity, using actual restrictions
and the direct-sum universal map. -/
def dualDirectSum {ι : Type} [Fintype ι] (V : ι → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module E (V i)] :
    Module.Dual E (DirectSum ι V) ≃ₗ[E] DirectSum ι (fun i => Module.Dual E (V i)) where
  toFun phi := (DirectSum.linearEquivFunOnFintype E ι (fun i => Module.Dual E (V i))).symm
    (fun i => phi.comp (DirectSum.lof E ι V i))
  invFun phi := DirectSum.toModule E ι E (fun i => phi i)
  left_inv phi := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change DirectSum.toModule E ι E (fun i => phi.comp (DirectSum.lof E ι V i))
      (DirectSum.lof E ι V i x) = phi (DirectSum.lof E ι V i x)
    rw [DirectSum.toModule_lof]
    rfl
  right_inv phi := by
    apply DFinsupp.ext
    intro i
    apply LinearMap.ext
    intro x
    change DirectSum.toModule E ι E (fun i => phi i) (DirectSum.lof E ι V i x) = phi i x
    rw [DirectSum.toModule_lof]
  map_add' phi psi := by
    apply DFinsupp.ext
    intro i
    apply LinearMap.ext
    intro x
    rfl
  map_smul' a phi := by
    apply DFinsupp.ext
    intro i
    apply LinearMap.ext
    intro x
    rfl

/-- The dual/direct-sum map is equivariant for the actual contragredient action. -/
def dualSumEquiv {ι : Type} [Fintype ι] (R : ι → FDRep E G) :
    Representation.Equiv (dualRepresentation (finiteSum R)).ρ
      (finiteSum (fun i => dualRepresentation (R i))).ρ where
  toLinearEquiv := dualDirectSum (fun i => (R i).V)
  isIntertwining' g := by
    apply LinearMap.ext
    intro phi
    change Module.Dual E (DirectSum ι (fun i => (R i).V)) at phi
    apply DFinsupp.ext
    intro i
    apply LinearMap.ext
    intro x
    change phi (DirectSum.lmap (fun j => (R j).ρ g⁻¹) (DirectSum.lof E ι (fun j => (R j).V) i x)) =
      phi (DirectSum.lof E ι (fun j => (R j).V) i ((R i).ρ g⁻¹ x))
    rw [DirectSum.lmap_lof]

/-- Ordinary dual profiles are constructed using actual dual distributivity. -/
theorem dual_profile (C : CharacterOperations chi) {R : FDRep E G}
    (hR : FiniteCharacterProfile chi R) : FiniteCharacterProfile chi (dualRepresentation R) := by
  obtain ⟨n, beta, ⟨eR⟩⟩ := hR
  let e := (dualEquiv (equivOfIso eR)).trans
    ((dualSumEquiv _).trans (finiteSumEquiv (fun i => C.dual (beta i))))
  exact (profile_iso (isoOfEquiv e)).mpr (finiteSum_profile _)

/-- Dual support negation is linked to the ORIGINAL decomposition coefficients. -/
theorem dual_phases (L : CharacterLaws chi) (C : CharacterOperations chi) {R : FDRep E G}
    (hR : FiniteCharacterProfile chi R) {alpha : PhaseField K}
    (ha : alpha ∈ homSupport chi (dualRepresentation R)) : -alpha ∈ homSupport chi R := by
  obtain ⟨n, beta, ⟨eR⟩⟩ := hR
  let e := (dualEquiv (equivOfIso eR)).trans
    ((dualSumEquiv _).trans (finiteSumEquiv (fun i => C.dual (beta i))))
  rw [homSupport_iso (isoOfEquiv e), L.finiteSum_support] at ha
  obtain ⟨i, hi⟩ := ha
  rw [homSupport_iso eR, L.finiteSum_support]
  exact ⟨i, by simp only [← hi, neg_neg]⟩

/-- Convert the ACTUAL FDRep morphism into the same equivariant linear map. -/
def intertwiningOfHom {R S : FDRep E G} (f : R ⟶ S) :
    Representation.IntertwiningMap R.ρ S.ρ :=
  ((FDRep.forget₂HomLinearEquiv R S).symm f).hom

abbrev groupModule (R : FDRep E G) := Representation.asModule R.ρ

def groupCarrierEquiv (R : FDRep E G) : groupModule R ≃ₗ[E] R.V :=
  Representation.asModuleEquiv R.ρ

/-- The standard group-ring linear map of an actual FDRep morphism. -/
def moduleMap {R S : FDRep E G} (f : R ⟶ S) :
    groupModule R →ₗ[E[G]] groupModule S :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ (intertwiningOfHom f)

/-- Every SAME rank-one character is simple as an actual group-ring module. -/
theorem character_simple (L : CharacterLaws chi) (beta : PhaseField K) :
    IsSimpleModule E[G] (groupModule (chi beta)) := by
  apply (isSimpleModule_iff E[G] (groupModule (chi beta))).mpr
  apply is_simple_module_of_finrank_eq_one (K := E)
  rw [(groupCarrierEquiv (chi beta)).finrank_eq]
  exact L.rank_one beta

/-- The actual representation direct sum agrees with the group-ring module
direct sum; this comparison is derived from its actual inclusions. -/
def sumModuleEquiv {ι : Type} [Fintype ι] (R : ι → FDRep E G) :
    groupModule (finiteSum R) ≃ₗ[E[G]] DirectSum ι (fun i => groupModule (R i)) := by
  let f := DirectSum.toModule E[G] ι (groupModule (finiteSum R))
    (fun i => moduleMap (sumInclusion R i))
  let e : DirectSum ι (fun i => groupModule (R i)) ≃ₗ[E] groupModule (finiteSum R) :=
    (DirectSum.congrLinearEquiv (fun i => groupCarrierEquiv (R i))).trans
      (groupCarrierEquiv (finiteSum R)).symm
  have h : f.restrictScalars E = e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change f (DirectSum.lof E[G] ι (fun i => groupModule (R i)) i x) =
      (groupCarrierEquiv (finiteSum R)).symm
        (DirectSum.lof E ι (fun i => (R i).V) i (groupCarrierEquiv (R i) x))
    rw [DirectSum.toModule_lof]
    rfl
  exact (LinearEquiv.ofBijective f (by change Function.Bijective (f.restrictScalars E); rw [h]; exact e.bijective)).symm

/-- Semisimplicity is PROVED for defined finite-character profiles;
there is no universal semisimplicity input and no finite-group assumption. -/
theorem profile_semisimple (L : CharacterLaws chi) {R : FDRep E G}
    (hR : FiniteCharacterProfile chi R) : IsSemisimpleModule E[G] (groupModule R) := by
  obtain ⟨n, beta, ⟨e⟩⟩ := hR
  let : ∀ i, IsSimpleModule E[G] (groupModule (chi (beta i))) := fun i => character_simple L (beta i)
  let : ∀ i, IsSemisimpleModule E[G] (groupModule (chi (beta i))) := fun i => inferInstance
  let : IsSemisimpleModule E[G] (DirectSum (Fin n) (fun i => groupModule (chi (beta i)))) := by
    change IsSemisimpleModule E[G] (Π₀ i : Fin n, groupModule (chi (beta i)))
    infer_instance
  let : IsSemisimpleModule E[G] (groupModule (finiteSum (fun i => chi (beta i)))) :=
    IsSemisimpleModule.congr (sumModuleEquiv _)
  exact IsSemisimpleModule.of_injective (moduleMap e.hom) (by
    intro x y h
    have hu := congrArg (moduleMap e.inv) h
    have he := congrArg underlying e.hom_inv_id
    have hx := congrArg (fun f => f x) he
    have hy := congrArg (fun f => f y) he
    change underlying e.inv (underlying e.hom x) = underlying e.inv (underlying e.hom y) at hu
    simpa only [underlying_comp, underlying_id, LinearMap.comp_apply, LinearMap.id_apply] using
      hx.symm.trans (hu.trans hy))

/-- Split the actual finite tensor at0 and reindex the actual remaining factors. -/
def tensorFinConsEquiv {n : ℕ} (R : Fin (n + 1) → FDRep E G) :
    Representation.Equiv (indexedTensor R).ρ
      (tensor (R 0) (indexedTensor (fun i : Fin n => R i.succ))).ρ :=
  (indexedTensorSplit R 0).trans
    (tensorEquiv (.refl _) (indexedTensorEquiv
      (fun j : ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1))) => R j.val)
      (fun i : Fin n => R i.succ) (tailEquiv n).symm
      (fun j => representationEquivOfEq (congrArg R (Fin.succ_pred j.val j.property).symm))))

/-- Fin-indexed actual tensor profile and support, proved by finite induction. -/
theorem fin_tensor_properties (L : CharacterLaws chi) (C : CharacterOperations chi) (n : ℕ)
    (R : Fin n → FDRep E G) (hR : ∀ i, FiniteCharacterProfile chi (R i)) :
    FiniteCharacterProfile chi (indexedTensor R) ∧
      ∀ alpha ∈ homSupport chi (indexedTensor R), ∃ beta : Fin n → PhaseField K,
        (∀ i, beta i ∈ homSupport chi (R i)) ∧ alpha = ∑ i, beta i := by
  induction n with
  | zero =>
    let e := isoOfEquiv (indexedTensorEmptyEquiv R)
    have hu : Representation.IsTrivial (𝟙_ (FDRep E G)).ρ := ⟨fun _ => rfl⟩
    refine ⟨(profile_iso e).mpr (trivial_profile L _ hu), ?_⟩
    intro alpha ha
    rw [homSupport_iso e] at ha
    have h0 : alpha = 0 := trivial_support_subset L _ hu ha
    refine ⟨Fin.elim0, (fun i => Fin.elim0 i), ?_⟩
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using h0
  | succ n ih =>
    have ht := ih (fun i => R i.succ) (fun i => hR i.succ)
    let e := isoOfEquiv (tensorFinConsEquiv R)
    refine ⟨(profile_iso e).mpr (binary_tensor_profile C (hR 0) ht.1), ?_⟩
    intro alpha ha
    rw [homSupport_iso e] at ha
    obtain ⟨beta, hb, gamma, hg, he⟩ := binary_tensor_phases L C (hR 0) ht.1 ha
    obtain ⟨tail, htail, hsum⟩ := ht.2 gamma hg
    refine ⟨Fin.cons beta tail, ?_, ?_⟩
    · intro i
      refine Fin.cases hb (fun j => htail j) i
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simpa only [Fin.cons_succ, ← hsum] using he

/-- Arbitrary finite-indexed tensor profile and ORIGINAL-factor support. -/
theorem indexed_tensor_properties (L : CharacterLaws chi) (C : CharacterOperations chi)
    {ι : Type} [Fintype ι] (R : ι → FDRep E G)
    (hR : ∀ i, FiniteCharacterProfile chi (R i)) :
    FiniteCharacterProfile chi (indexedTensor R) ∧
      ∀ alpha ∈ homSupport chi (indexedTensor R), ∃ beta : ι → PhaseField K,
        (∀ i, beta i ∈ homSupport chi (R i)) ∧ alpha = ∑ i, beta i := by
  let e := Fintype.equivFin ι
  have hf := fin_tensor_properties L C (Fintype.card ι) (fun j => R (e.symm j))
    (fun j => hR (e.symm j))
  let er := isoOfEquiv (indexedTensorReindex R e)
  refine ⟨(profile_iso er).mpr hf.1, ?_⟩
  intro alpha ha
  rw [homSupport_iso er] at ha
  obtain ⟨beta, hb, he⟩ := hf.2 alpha ha
  refine ⟨fun i => beta (e i), ?_, he.trans (e.sum_comp beta).symm⟩
  intro i
  simpa only [Equiv.symm_apply_apply] using hb (e i)

/-- Exact original selected-tensor profile field, with empty selections included. -/
theorem tensor_profile (L : CharacterLaws chi) (C : CharacterOperations chi)
    {ι : Type} (s : Finset ι) (R : ι → FDRep E G)
    (hR : ∀ i ∈ s, FiniteCharacterProfile chi (R i)) :
    FiniteCharacterProfile chi (selectedTensor s R) :=
  (indexed_tensor_properties L C (fun i : s => R i.val) (fun i => hR i.val i.property)).1

/-- Exact original selected-tensor support field. Coefficients outside the
selection extend by0; every selected coefficient is linked to its ORIGINAL factor. -/
theorem tensor_phases (L : CharacterLaws chi) (C : CharacterOperations chi)
    {ι : Type} (s : Finset ι) (R : ι → FDRep E G)
    (hR : ∀ i ∈ s, FiniteCharacterProfile chi (R i)) {alpha : PhaseField K}
    (ha : alpha ∈ homSupport chi (selectedTensor s R)) :
    ∃ beta : ι → PhaseField K, (∀ i ∈ s, beta i ∈ homSupport chi (R i)) ∧
      alpha = ∑ i ∈ s, beta i := by
  obtain ⟨beta, hb, he⟩ := (indexed_tensor_properties L C (fun i : s => R i.val)
    (fun i => hR i.val i.property)).2 alpha ha
  let b (i : ι) : PhaseField K := if hi : i ∈ s then beta ⟨i, hi⟩ else 0
  refine ⟨b, ?_, ?_⟩
  · intro i hi
    simpa only [b, dite_eq_left hi] using hb ⟨i, hi⟩
  · rw [← Finset.sum_coe_sort]
    exact he.trans (Finset.sum_congr rfl (fun i _ => by simp only [b, dite_eq_left i.property]))

/-- Group-ring linear equivalences induce actual equivariant equivalences
on the ORIGINAL representation objects. -/
def equivOfModuleEquiv {R S : FDRep E G} (e : groupModule R ≃ₗ[E[G]] groupModule S) :
    Representation.Equiv R.ρ S.ρ :=
  ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm e.toLinearMap).ofBijective
    (by with_unfolding_all exact e.bijective)

/-- An actual subquotient of a profiled object admits an ACTUAL equivariant
embedding into that same object: the quotient is split using proved semisimplicity. -/
theorem subquotient_embedding (L : CharacterLaws chi) {R S : FDRep E G}
    (h : IsSubquotient R S) (hS : FiniteCharacterProfile chi S) :
    ∃ j : groupModule R →ₗ[E[G]] groupModule S, Function.Injective j := by
  obtain ⟨W, i, q, hi, hq⟩ := h
  let im := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i
  let qm := Representation.IntertwiningMap.equivLinearMapAsModule _ _ q
  let : IsSemisimpleModule E[G] (groupModule S) := profile_semisimple L hS
  let : IsSemisimpleModule E[G] (groupModule W) :=
    IsSemisimpleModule.of_injective im (by with_unfolding_all exact hi)
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property qm
    (by with_unfolding_all exact hq) (LinearMap.id : groupModule R →ₗ[E[G]] groupModule R)
  refine ⟨im.comp s, hi.comp ?_⟩
  intro x y hxy
  have hh := congrArg qm hxy
  have hx := congrArg (fun f => f x) hs
  have hy := congrArg (fun f => f y) hs
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hx.symm.trans (hh.trans hy)

/-- Nonzero maps into literal module sums have a nonzero component. -/
theorem module_sum_nonzero_component {ι : Type} [Fintype ι]
    {M : Type v} [AddCommGroup M] [Module E[G] M]
    (R : ι → FDRep E G) (f : M →ₗ[E[G]] DirectSum ι (fun i => groupModule (R i)))
    (hf : f ≠ 0) : ∃ i,
      (DirectSum.component E[G] ι (fun i => groupModule (R i)) i).comp f ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro i
  exact congrArg (fun f => f x) (h i)

/-- Every simple module embedded in a defined character sum is isomorphic
to ONE of its SAME characters; only actual component maps and Schur's lemma are used. -/
theorem simple_component_character (L : CharacterLaws chi) {n : ℕ}
    (beta : Fin n → PhaseField K) {M : Type v} [AddCommGroup M] [Module E[G] M]
    [IsSimpleModule E[G] M]
    (f : M →ₗ[E[G]] DirectSum (Fin n) (fun i => groupModule (chi (beta i))))
    (hf : Function.Injective f) :
    ∃ i, Nonempty (M ≃ₗ[E[G]] groupModule (chi (beta i))) := by
  have hn : f ≠ 0 := by
    intro h
    have : Subsingleton M := ⟨fun x y => hf (by simp only [h, LinearMap.zero_apply])⟩
    exact not_nontrivial_iff_subsingleton.mpr this (IsSimpleModule.nontrivial E[G] M)
  obtain ⟨i, hi⟩ := module_sum_nonzero_component _ f hn
  let : IsSimpleModule E[G] (groupModule (chi (beta i))) := character_simple L _
  exact ⟨i, ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hi)⟩⟩

/-- Exact original subquotient-profile rule, from proved semisimplicity
and finite simple-module decomposition; no universal decomposition law is input. -/
theorem subquotient_profile (L : CharacterLaws chi) (R S : FDRep E G)
    (h : IsSubquotient R S) (hS : FiniteCharacterProfile chi S) :
    FiniteCharacterProfile chi R := by
  obtain ⟨j, hj⟩ := subquotient_embedding L h hS
  let : IsSemisimpleModule E[G] (groupModule S) := profile_semisimple L hS
  let : IsSemisimpleModule E[G] (groupModule R) := IsSemisimpleModule.of_injective j hj
  let : Module.Finite E[G] (groupModule R) := Module.Finite.of_restrictScalars_finite E E[G] _
  obtain ⟨n, V, e, hV⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp E[G] (groupModule R)
  obtain ⟨m, beta, ⟨eS⟩⟩ := hS
  let embed := (sumModuleEquiv (fun i => chi (beta i))).toLinearMap.comp
    ((moduleMap eS.hom).comp j)
  have hembed : Function.Injective embed := by
    apply (sumModuleEquiv _).injective.comp
    apply (Function.Injective.comp ?_ hj)
    intro x y hxy
    have hh := congrArg (moduleMap eS.inv) hxy
    have he := congrArg underlying eS.hom_inv_id
    have hx := congrArg (fun f => f x) he
    have hy := congrArg (fun f => f y) he
    simpa only [underlying_comp, underlying_id, LinearMap.comp_apply, LinearMap.id_apply] using
      hx.symm.trans (hh.trans hy)
  have hc (i : Fin n) : ∃ b, Nonempty (V i ≃ₗ[E[G]] groupModule (chi b)) := by
    let : IsSimpleModule E[G] (V i) := hV i
    obtain ⟨a, ha⟩ := simple_component_character L beta (embed.comp (V i).subtype)
      (hembed.comp (V i).injective_subtype)
    exact ⟨beta a, ha⟩
  choose gamma ec using hc
  let er := e.trans ((DirectSum.congrLinearEquiv (fun i => (ec i).some)).trans
    (sumModuleEquiv (fun i => chi (gamma i))).symm)
  exact ⟨n, gamma, ⟨isoOfEquiv (equivOfModuleEquiv er)⟩⟩

/-- Canonical Hom support is monotone under every ACTUAL injective equivariant map. -/
theorem homSupport_injective {R S : FDRep E G}
    (f : Representation.IntertwiningMap R.ρ S.ρ) (hf : Function.Injective f) :
    homSupport chi R ⊆ homSupport chi S := by
  rintro beta ⟨g, hg⟩
  refine ⟨g ≫ repHom f, ?_⟩
  intro h
  apply hg
  apply PhaseDataFromOriginalCharacters.hom_ext
  apply LinearMap.ext
  intro x
  apply hf
  have he := congrArg (fun h => underlying h x) h
  with_unfolding_all simpa only [underlying_comp, underlying_repHom, underlying_zero, LinearMap.comp_apply,
    LinearMap.zero_apply, map_zero, Representation.IntertwiningMap.toLinearMap_apply] using he

/-- Exact original subquotient-support rule, from the constructed SAME-object
embedding rather than an independently supplied phase-subset law. -/
theorem subquotient_phases (L : CharacterLaws chi) (R S : FDRep E G)
    (h : IsSubquotient R S) (hS : FiniteCharacterProfile chi S) :
    homSupport chi R ⊆ homSupport chi S := by
  obtain ⟨j, hj⟩ := subquotient_embedding L h hS
  exact homSupport_injective
    ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm j)
    (by with_unfolding_all exact hj)

/-- ALL TEN original phase rules are derived on the canonical PhaseData.
The only external laws are the SAME character rank/separation/triviality
and actual tensor/dual character equivalences, never TypeIII target conclusions. -/
theorem phaseRules [CharZero E] (L : CharacterLaws chi) (C : CharacterOperations chi) :
    PhaseRules (characterPhaseData chi) where
  transport := transport
  sum_profile := sum_profile
  sum_phases R _ := sum_phases R
  tensor_profile := tensor_profile L C
  tensor_phases s R hR _ := tensor_phases L C s R hR
  dual_profile _ := dual_profile C
  dual_phases _ hR _ := dual_phases L C hR
  subquotient_profile := subquotient_profile L
  subquotient_phases := subquotient_phases L
  map_to_trivial_zero := map_to_trivial_zero L

/-- Apply the ten derived algebraic rules to the SAME original B/J/AS
family of canonicalPD. No original PhaseRules record is retained. -/
theorem canonicalPhaseRules [CharZero E] {K0 : Type} [Field K0]
    (B : SourceInverseImageSystem.System.{0,mu} K0)
    (J : B.Obj .parameter ⥤ FDRep E G) (as : B.Obj .line)
    (L : CharacterLaws (oldCharacter (J := J) as))
    (C : CharacterOperations (oldCharacter (J := J) as)) :
    PhaseRules (canonicalPD B J as) := phaseRules L C

end PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters

#print axioms PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters.transport
#print axioms PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters.sum_profile
#print axioms PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters.sum_phases
#print axioms PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters.nonzero_map_shared_support
#print axioms PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters.phaseRules
#print axioms PrimeGap182.TypeIII.PhaseRulesFromSeparatedCharacters.canonicalPhaseRules
