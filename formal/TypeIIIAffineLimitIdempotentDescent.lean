import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import TypeIIINilpotentThickeningIdempotents

/-!
# Actual idempotent and clopen descent along an affine-transition limit

Let D be a cofiltered diagram of qcqs schemes with affine transition
maps, and let c be an actual limit cone. Every idempotent in the original
global-section ring of c.pt comes from an idempotent at one stage.
Representatives from two stages whose original pullbacks agree become
equal after restriction to a common later stage. The same existence
and equality statements hold for literal inverse images of clopen sets.

The proof uses the existing section-descent theorem for the actual
limit and eventual vanishing of the original idempotent defect or
difference. The clopen assertions use the proved global-idempotent
classification and its original restriction naturality.

This proves the limit-descent step used in the approximation argument
for proper section existence. It does not construct Noetherian models,
assume a proper formal-functions comparison, or prove proper section
existence itself. No properness or Noetherian hypothesis occurs here.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.AffineLimitIdempotentDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NilpotentThickeningIdempotents SchemeIdempotentClopens
open TopologicalSpace
open scoped AlgebraicGeometry

variable {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u}) (c : Cone D)

/-- The original section pullbacks satisfy the actual limit-cone identity. -/
theorem projection_appTop_map {i j : J} (f : j ⟶ i) (a : Γ(D.obj i, ⊤)) :
    (c.π.app j).appTop ((D.map f).appTop a) = (c.π.app i).appTop a := by
  change (c.π.app j ≫ D.map f).appTop a = (c.π.app i).appTop a
  rw [c.w f]

variable (hc : IsLimit c) [IsCofiltered J]
  [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i : J, CompactSpace (D.obj i)]

include hc

/-- Two original sections at one stage that agree on the limit agree at a later stage. -/
theorem exists_eventual_section_eq {i : J} (a b : Γ(D.obj i, ⊤))
    (h : (c.π.app i).appTop a = (c.π.app i).appTop b) :
    ∃ (j : J) (f : j ⟶ i), (D.map f).appTop a = (D.map f).appTop b := by
  obtain ⟨j, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (a - b)
    (by simpa only [map_sub, sub_eq_zero] using h)
  exact ⟨j, f, by simpa only [map_sub, sub_eq_zero] using hf⟩

/-- Original section representatives at different stages have a common stage of equality. -/
theorem exists_common_refinement_section {i j : J}
    (a : Γ(D.obj i, ⊤)) (b : Γ(D.obj j, ⊤))
    (h : (c.π.app i).appTop a = (c.π.app j).appTop b) :
    ∃ (k : J) (f : k ⟶ i) (g : k ⟶ j), (D.map f).appTop a = (D.map g).appTop b := by
  obtain ⟨k, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hk : (c.π.app k).appTop ((D.map f).appTop a) =
      (c.π.app k).appTop ((D.map g).appTop b) := by
    rw [projection_appTop_map D c f, projection_appTop_map D c g]
    exact h
  obtain ⟨l, s, hs⟩ := exists_eventual_section_eq D c hc
    ((D.map f).appTop a) ((D.map g).appTop b) hk
  refine ⟨l, s ≫ f, s ≫ g, ?_⟩
  simpa only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hs

section

variable [∀ i : J, QuasiSeparatedSpace (D.obj i)]

/-- Every actual global idempotent of the limit descends with its original section value. -/
theorem exists_stage_idempotent (e : Γ(c.pt, ⊤)) (he : IsIdempotentElem e) :
    ∃ (i : J) (a : Γ(D.obj i, ⊤)),
      IsIdempotentElem a ∧ (c.π.app i).appTop a = e := by
  obtain ⟨i, a, ha⟩ := exists_appTop_π_eq_of_isLimit D c hc e
  have heq : e * e = e := he
  have hz : (c.π.app i).appTop (a * a - a) = 0 := by
    rw [map_sub, map_mul, ← ha, heq, sub_self]
  obtain ⟨j, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (a * a - a) hz
  refine ⟨j, (D.map f).appTop a, ?_, ?_⟩
  · change (D.map f).appTop a * (D.map f).appTop a = (D.map f).appTop a
    simpa only [map_sub, map_mul, sub_eq_zero] using hf
  · rw [projection_appTop_map D c f]
    exact ha.symm

/-- Descent in the original bundled global-idempotent spaces and original restriction maps. -/
theorem exists_stage (e : GlobalIdempotents c.pt) :
    ∃ (i : J) (a : GlobalIdempotents (D.obj i)), idempotentRestriction (c.π.app i) a = e := by
  obtain ⟨i, a, ha, he⟩ := exists_stage_idempotent D c hc e.val e.property
  exact ⟨i, ⟨a, ha⟩, Subtype.ext he⟩

end

/-- Equality of original idempotent pullbacks is witnessed at an actual common stage. -/
theorem exists_common_refinement_idempotent {i j : J}
    (a : GlobalIdempotents (D.obj i)) (b : GlobalIdempotents (D.obj j))
    (h : idempotentRestriction (c.π.app i) a = idempotentRestriction (c.π.app j) b) :
    ∃ (k : J) (f : k ⟶ i) (g : k ⟶ j),
      idempotentRestriction (D.map f) a = idempotentRestriction (D.map g) b := by
  obtain ⟨k, f, g, hfg⟩ := exists_common_refinement_section D c hc a.val b.val
    (congrArg Subtype.val h)
  exact ⟨k, f, g, Subtype.ext hfg⟩

section

variable [∀ i : J, QuasiSeparatedSpace (D.obj i)]

/-- Every clopen of the actual limit is the literal inverse image of a clopen at one stage. -/
theorem exists_stage_clopen (U : Clopens c.pt) :
    ∃ (i : J) (V : Clopens (D.obj i)), clopenPullback (c.π.app i) V = U := by
  obtain ⟨i, a, ha⟩ := exists_stage D c hc ((globalIdempotentClopenEquiv c.pt).symm U)
  refine ⟨i, globalIdempotentClopenEquiv (D.obj i) a, ?_⟩
  rw [← globalIdempotentClopenEquiv_naturality]
  change globalIdempotentClopenEquiv c.pt (idempotentRestriction (c.π.app i) a) = U
  rw [ha, OrderIso.apply_symm_apply]

end

/-- Equality of two literal clopen pullbacks is witnessed after original maps from a common stage. -/
theorem exists_common_refinement_clopen {i j : J}
    (U : Clopens (D.obj i)) (V : Clopens (D.obj j))
    (h : clopenPullback (c.π.app i) U = clopenPullback (c.π.app j) V) :
    ∃ (k : J) (f : k ⟶ i) (g : k ⟶ j),
      clopenPullback (D.map f) U = clopenPullback (D.map g) V := by
  let a := (globalIdempotentClopenEquiv (D.obj i)).symm U
  let b := (globalIdempotentClopenEquiv (D.obj j)).symm V
  have hab : idempotentRestriction (c.π.app i) a = idempotentRestriction (c.π.app j) b := by
    apply (globalIdempotentClopenEquiv c.pt).injective
    unfold idempotentRestriction
    rw [globalIdempotentClopenEquiv_naturality, globalIdempotentClopenEquiv_naturality]
    simpa only [a, b, OrderIso.apply_symm_apply] using h
  obtain ⟨k, f, g, hfg⟩ := exists_common_refinement_idempotent D c hc a b hab
  refine ⟨k, f, g, ?_⟩
  have hfg' := congrArg (globalIdempotentClopenEquiv (D.obj k)) hfg
  unfold idempotentRestriction at hfg'
  rw [globalIdempotentClopenEquiv_naturality, globalIdempotentClopenEquiv_naturality] at hfg'
  simpa only [a, b, OrderIso.apply_symm_apply] using hfg'

#print axioms projection_appTop_map
#print axioms exists_eventual_section_eq
#print axioms exists_common_refinement_section
#print axioms exists_stage_idempotent
#print axioms exists_stage
#print axioms exists_common_refinement_idempotent
#print axioms exists_stage_clopen
#print axioms exists_common_refinement_clopen

end PrimeGap182.TypeIII.AffineLimitIdempotentDescent
