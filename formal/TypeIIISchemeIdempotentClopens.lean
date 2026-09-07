import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Global idempotents and clopens of a scheme

For every scheme X, idempotents of its original ring of global sections
correspond to clopen subsets of X.  The forward map is the basic open of
the section.  Surjectivity uses the original structure sheaf to glue 1
on the clopen and 0 on its complement; injectivity uses its actual germs
in local stalks and sheaf separatedness.

The resulting order isomorphism agrees with literal inverse image along
the canonical morphism X → Spec Γ(X, ⊤), and is natural for pullback of
global sections.  There are no properness, affineness, quasi-compactness,
reducedness, or nonemptiness hypotheses.  This does not assert extension
of clopens from a closed fiber of a proper scheme.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.SchemeIdempotentClopens

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

/-- A nonunit idempotent of a local ring is zero. -/
theorem idempotent_eq_zero_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) (h : ¬ IsUnit a) : a = 0 := by
  have hc : IsUnit (1 - a) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a h
  exact sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hc).mp ha.one_sub)

/-- In a local ring, the unit predicate determines an idempotent. -/
theorem idempotents_eq_of_isUnit_iff {R : Type*} [CommRing R] [IsLocalRing R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : IsUnit a ↔ IsUnit b) : a = b := by
  by_cases hunit : IsUnit a
  · exact ((IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp ha).trans
      ((IsIdempotentElem.iff_eq_one_of_isUnit (h.mp hunit)).mp hb).symm
  · exact (idempotent_eq_zero_of_not_isUnit ha hunit).trans
      (idempotent_eq_zero_of_not_isUnit hb (fun hunitb => hunit (h.mpr hunitb))).symm

/-- Equal basic opens of global idempotents give equal actual sections. -/
theorem basicOpen_injective_on_idempotents (X : Scheme.{u})
    {e f : Γ(X, ⊤)} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : X.basicOpen e = X.basicOpen f) : e = f := by
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ e f
  intro x _
  change X.presheaf.germ ⊤ x trivial e = X.presheaf.germ ⊤ x trivial f
  apply idempotents_eq_of_isUnit_iff
    (he.map (X.presheaf.germ ⊤ x trivial).hom)
    (hf.map (X.presheaf.germ ⊤ x trivial).hom)
  exact (X.mem_basicOpen_top e x).symm.trans
    ((show x ∈ X.basicOpen e ↔ x ∈ X.basicOpen f by rw [h]).trans
      (X.mem_basicOpen_top f x))

/-- The original structure sheaf glues 1 on a clopen and 0 on its complement. -/
theorem exists_section_of_clopen (X : Scheme.{u}) (U : Clopens X) :
    ∃ e : Γ(X, ⊤),
      X.presheaf.map (homOfLE (le_top : U.toOpens ≤ ⊤)).op e = 1 ∧
      X.presheaf.map (homOfLE (le_top : (Uᶜ).toOpens ≤ ⊤)).op e = 0 := by
  let V : Bool → X.Opens := fun b => if b then U.toOpens else (Uᶜ).toOpens
  let sf : (b : Bool) → Γ(X, V b) := fun b => if b then 1 else 0
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    by_cases hx : x ∈ U
    · exact Opens.mem_iSup.mpr ⟨true, hx⟩
    · exact Opens.mem_iSup.mpr ⟨false, hx⟩
  have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro i j
    cases i <;> cases j
    · simp [sf]
    · apply TopCat.Presheaf.section_ext X.sheaf (V false ⊓ V true)
      intro x hx
      exact False.elim (hx.1 hx.2)
    · apply TopCat.Presheaf.section_ext X.sheaf (V true ⊓ V false)
      intro x hx
      exact False.elim (hx.2 hx.1)
    · simp [sf]
  obtain ⟨e, he, _⟩ : ∃! e : Γ(X, ⊤),
      ∀ b : Bool, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b :=
    X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcover sf hcompatible
  exact ⟨e, he true, he false⟩

/-- Every clopen is the actual basic open of a global idempotent. -/
theorem exists_idempotent_of_clopen (X : Scheme.{u}) (U : Clopens X) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U.toOpens := by
  obtain ⟨e, heU, heV⟩ := exists_section_of_clopen X U
  have hcover : (⊤ : X.Opens) ≤ U.toOpens ⊔ (Uᶜ).toOpens := by
    intro x _
    exact em (x ∈ U)
  have he : IsIdempotentElem e := by
    change e * e = e
    apply X.sheaf.eq_of_locally_eq₂
      (homOfLE (le_top : U.toOpens ≤ ⊤))
      (homOfLE (le_top : (Uᶜ).toOpens ≤ ⊤)) hcover
    · change X.presheaf.map (homOfLE (le_top : U.toOpens ≤ ⊤)).op (e * e) =
        X.presheaf.map (homOfLE (le_top : U.toOpens ≤ ⊤)).op e
      rw [map_mul, heU, mul_one]
    · change X.presheaf.map (homOfLE (le_top : (Uᶜ).toOpens ≤ ⊤)).op (e * e) =
        X.presheaf.map (homOfLE (le_top : (Uᶜ).toOpens ≤ ⊤)).op e
      rw [map_mul, heV, mul_zero]
  have hU := congrArg (fun s : Γ(X, U.toOpens) => X.basicOpen s) heU
  rw [X.basicOpen_res, X.basicOpen_one] at hU
  have hV := congrArg (fun s : Γ(X, (Uᶜ).toOpens) => X.basicOpen s) heV
  rw [X.basicOpen_res, X.basicOpen_zero] at hV
  refine ⟨e, he, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hnot
    have hxV : x ∈ (Uᶜ).toOpens ⊓ X.basicOpen e := ⟨hnot, hx⟩
    rw [hV] at hxV
    exact hxV
  · intro hx
    have hxU : x ∈ U.toOpens ⊓ X.basicOpen e := by
      rw [hU]
      exact hx
    exact hxU.2

/-- Literal inverse image of a clopen under an actual scheme morphism. -/
def clopenPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Clopens Y) : Clopens X :=
  ⟨f ⁻¹' (U : Set Y), U.isClopen.preimage f.continuous⟩

/-- The clopen pullback has the original set-theoretic inverse-image carrier. -/
theorem clopenPullback_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Clopens Y) :
    (clopenPullback f U : Set X) = f ⁻¹' (U : Set Y) := rfl

/-- Actual clopen pullback along the canonical global-sections morphism. -/
def toSpecΓClopenPullback (X : Scheme.{u})
    (U : Clopens (PrimeSpectrum Γ(X, ⊤))) : Clopens X :=
  clopenPullback X.toSpecΓ U

/-- This map is literally inverse image under X → Spec Γ(X, ⊤). -/
theorem toSpecΓClopenPullback_coe (X : Scheme.{u})
    (U : Clopens (PrimeSpectrum Γ(X, ⊤))) :
    (toSpecΓClopenPullback X U : Set X) =
      X.toSpecΓ ⁻¹' (U : Set (PrimeSpectrum Γ(X, ⊤))) := rfl

/-- On an idempotent basic open, actual pullback is the basic open of that section. -/
theorem toSpecΓClopenPullback_idempotent_toOpens (X : Scheme.{u})
    (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) :
    (toSpecΓClopenPullback X (PrimeSpectrum.isIdempotentElemEquivClopens e)).toOpens =
      X.basicOpen e.1 := by
  change X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen e.1 = X.basicOpen e.1
  exact X.toSpecΓ_preimage_basicOpen e.1

/-- The canonical global-sections morphism induces a bijection on clopens. -/
theorem toSpecΓClopenPullback_bijective (X : Scheme.{u}) :
    Function.Bijective (toSpecΓClopenPullback X) := by
  constructor
  · intro U V h
    obtain ⟨e, rfl⟩ :=
      (PrimeSpectrum.isIdempotentElemEquivClopens (R := Γ(X, ⊤))).surjective U
    obtain ⟨f, rfl⟩ :=
      (PrimeSpectrum.isIdempotentElemEquivClopens (R := Γ(X, ⊤))).surjective V
    have hbasic := congrArg Clopens.toOpens h
    rw [toSpecΓClopenPullback_idempotent_toOpens,
      toSpecΓClopenPullback_idempotent_toOpens] at hbasic
    have hef : e = f :=
      Subtype.ext (basicOpen_injective_on_idempotents X e.2 f.2 hbasic)
    exact congrArg PrimeSpectrum.isIdempotentElemEquivClopens hef
  · intro U
    obtain ⟨e, he, hbasic⟩ := exists_idempotent_of_clopen X U
    refine ⟨PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩, ?_⟩
    apply Clopens.ext
    exact congrArg (fun V : X.Opens => (V : Set X))
      ((toSpecΓClopenPullback_idempotent_toOpens X ⟨e, he⟩).trans hbasic)

/-- Clopen pullback along the original canonical morphism is an order isomorphism. -/
def toSpecΓClopenOrderIso (X : Scheme.{u}) :
    Clopens (PrimeSpectrum Γ(X, ⊤)) ≃o Clopens X where
  toEquiv := Equiv.ofBijective (toSpecΓClopenPullback X)
    (toSpecΓClopenPullback_bijective X)
  map_rel_iff' := by
    intro U V
    constructor
    · intro h
      apply inf_eq_left.mp
      apply (toSpecΓClopenPullback_bijective X).injective
      change toSpecΓClopenPullback X U ⊓ toSpecΓClopenPullback X V =
        toSpecΓClopenPullback X U
      exact inf_eq_left.mpr h
    · intro h x hx
      exact h hx

/-- Bundling the map as an order isomorphism does not change its value. -/
theorem toSpecΓClopenOrderIso_apply (X : Scheme.{u})
    (U : Clopens (PrimeSpectrum Γ(X, ⊤))) :
    toSpecΓClopenOrderIso X U = toSpecΓClopenPullback X U := rfl

/-- Global idempotents, with their existing canonical order, classify clopens. -/
def globalIdempotentClopenEquiv (X : Scheme.{u}) :
    {e : Γ(X, ⊤) // IsIdempotentElem e} ≃o Clopens X :=
  (PrimeSpectrum.isIdempotentElemEquivClopens (R := Γ(X, ⊤))).trans
    (toSpecΓClopenOrderIso X)

/-- The classified clopen is precisely the actual basic open of the global section. -/
theorem globalIdempotentClopenEquiv_toOpens (X : Scheme.{u})
    (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) :
    (globalIdempotentClopenEquiv X e).toOpens = X.basicOpen e.1 :=
  toSpecΓClopenPullback_idempotent_toOpens X e

/-- The classification has the original basic-open carrier. -/
theorem globalIdempotentClopenEquiv_coe (X : Scheme.{u})
    (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) :
    (globalIdempotentClopenEquiv X e : Set X) = (X.basicOpen e.1 : Set X) :=
  congrArg (fun V : X.Opens => (V : Set X)) (globalIdempotentClopenEquiv_toOpens X e)

/-- The inverse classification returns an idempotent whose actual basic open is prescribed. -/
theorem globalIdempotentClopenEquiv_symm_basicOpen (X : Scheme.{u}) (U : Clopens X) :
    X.basicOpen ((globalIdempotentClopenEquiv X).symm U).1 = U.toOpens := by
  rw [← globalIdempotentClopenEquiv_toOpens, OrderIso.apply_symm_apply]

/-- Classification commutes with actual pullback of global sections and clopens. -/
theorem globalIdempotentClopenEquiv_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : {e : Γ(Y, ⊤) // IsIdempotentElem e}) :
    globalIdempotentClopenEquiv X ⟨f.appTop e.1, e.2.map f.appTop.hom⟩ =
      clopenPullback f (globalIdempotentClopenEquiv Y e) := by
  apply Clopens.ext
  rw [globalIdempotentClopenEquiv_coe, clopenPullback_coe,
    globalIdempotentClopenEquiv_coe]
  exact congrArg (fun V : X.Opens => (V : Set X))
    (Scheme.preimage_basicOpen_top f e.1).symm

/-- The literal canonical clopen pullbacks commute with the original Γ-Spec naturality square. -/
theorem toSpecΓClopenPullback_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Clopens (PrimeSpectrum Γ(Y, ⊤))) :
    clopenPullback f (toSpecΓClopenPullback Y U) =
      toSpecΓClopenPullback X (clopenPullback (Spec.map f.appTop) U) := by
  ext x
  change (f ≫ Y.toSpecΓ) x ∈ U ↔ (X.toSpecΓ ≫ Spec.map f.appTop) x ∈ U
  rw [Scheme.toSpecΓ_naturality f]

end PrimeGap182.TypeIII.SchemeIdempotentClopens

#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.idempotent_eq_zero_of_not_isUnit
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.idempotents_eq_of_isUnit_iff
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.basicOpen_injective_on_idempotents
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.exists_section_of_clopen
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.exists_idempotent_of_clopen
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.clopenPullback
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.clopenPullback_coe
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenPullback
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenPullback_coe
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenPullback_idempotent_toOpens
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenPullback_bijective
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenOrderIso
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenOrderIso_apply
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.globalIdempotentClopenEquiv
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.globalIdempotentClopenEquiv_toOpens
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.globalIdempotentClopenEquiv_coe
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.globalIdempotentClopenEquiv_symm_basicOpen
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.globalIdempotentClopenEquiv_naturality
#print axioms PrimeGap182.TypeIII.SchemeIdempotentClopens.toSpecΓClopenPullback_naturality
