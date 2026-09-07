import TypeIIIEtaleSectionsRestriction
import TypeIIIProperLocalClosedFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Injectivity of actual section restriction to the closed fiber

For a universally closed scheme morphism to the spectrum of a local ring,
the original restriction of an arbitrary module étale sheaf to the literal
closed fiber is injective on global sections.

Equality after restriction implies equality of the original geometric
germs through the actual inverse-image and skyscraper adjunctions.  The
filtered-colimit equality theorem produces pointed étale neighborhoods
where the sections agree.  Their images are open and cover the closed
fiber, hence cover the whole scheme.  Actual sheaf separatedness then
proves equality.  No henselian hypothesis, section-extension premise,
or proper-base-change theorem is used.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.ProperLocalSectionsInjective

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open ProperLocalClosedFiber

variable (R : Type u) [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} (q : X ⟶ Spec (.of R))

section Cover

variable [UniversallyClosed q]

/-- An actual étale family whose images cover the literal closed fiber
is a covering family of the original small étale site. -/
theorem covering_of_closedFiber {ι : Type*} {U : ι → X.Etale}
    (f : ∀ j, U j ⟶ EtaleCohomology.terminalObject X)
    (hf : Set.range (closedFiberι R q) ⊆ ⋃ j, Set.range (f j).left) :
    Sieve.ofArrows U f ∈ X.smallEtaleTopology (EtaleCohomology.terminalObject X) := by
  let V : X.Opens := ⟨⋃ j, Set.range (f j).left,
    isOpen_iUnion (fun j => (f j).left.isOpenMap.isOpen_range)⟩
  have hV : V = ⊤ := open_eq_top_of_closedFiber_subset R q V hf
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact congrArg (fun W : X.Opens => (W : Set X)) hV

end Cover

variable (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency false in
/-- Equality after original restriction is witnessed near every closed-fiber
point by an actual pointed étale neighborhood and equality of restrictions. -/
theorem neighborhood_of_restriction_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E))
    (a b : (EtaleCohomology.sections X E).obj F)
    (h : (EtaleSectionsRestriction.map (closedFiberι R q) E).app F a =
      (EtaleSectionsRestriction.map (closedFiberι R q) E).app F b)
    (z : closedFiber R q) :
    ∃ (U : X.Etale) (f : U ⟶ EtaleCohomology.terminalObject X) (x : U.left),
      f.left x = closedFiberι R q z ∧ F.obj.map f.op a = F.obj.map f.op b := by
  let σ := algebraicClosureEtalePointMap (closedFiber R q) z
  let Ψ := EtaleInverseImage.geometricPointComap (closedFiberι R q) σ
  let t := (Ψ.uniqueFiberObj (EtaleCohomology.terminalObject X)
    (EtaleCohomology.terminal_isTerminal X)).default
  have hunit := EtaleSectionsRestriction.unit_component_eq_of_map_eq
    (closedFiberι R q) E F a b h
  have hg := EtaleSectionsRestriction.comapGerm_eq_of_unit_component_eq
    (closedFiberι R q) E σ F (EtaleCohomology.terminalObject X) t a b hunit
  obtain ⟨U, f, y, _, hab⟩ :=
    (Ψ.toPresheafFiber_eq_iff' (EtaleCohomology.terminalObject X) t a b).mp hg
  let v := EtaleInverseImage.geometricFiberEquiv (closedFiberι R q) σ U y
  let ω : Spec (.of (AlgebraicClosure ((closedFiber R q).residueField z))) := default
  have hv : v.left ≫ U.hom = σ ≫ closedFiberι R q := Over.w v
  have hv' := congrArg (fun g => g ω) hv
  change U.hom (v.left ω) = closedFiberι R q (σ ω) at hv'
  rw [show σ ω = z from algebraicClosureEtalePointMap_apply _ _ _] at hv'
  have hf : f.left = U.hom := by
    have hf' := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 X = U.hom at hf'
    exact (Category.comp_id f.left).symm.trans hf'
  exact ⟨U, f, v.left ω, hf.symm ▸ hv', hab⟩

variable [UniversallyClosed q]

/-- The same original restriction map is injective for every module
étale sheaf, over a merely local base and a universally closed morphism. -/
theorem restriction_injective
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    Function.Injective ((EtaleSectionsRestriction.map (closedFiberι R q) E).app F) := by
  classical
  intro a b h
  choose U f x hx hab using neighborhood_of_restriction_eq R q E F a b h
  have hcover : Sieve.ofArrows U f ∈
      X.smallEtaleTopology (EtaleCohomology.terminalObject X) :=
    covering_of_closedFiber R q f (by
      rintro _ ⟨z, rfl⟩
      exact Set.mem_iUnion.mpr ⟨z, x z, hx z⟩)
  exact EtaleSectionsRestriction.section_ext_of_cover E F f hcover a b hab

/-- Categorical monomorphism of each component of that original restriction. -/
theorem restriction_app_mono
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} E)) :
    Mono ((EtaleSectionsRestriction.map (closedFiberι R q) E).app F) :=
  (ModuleCat.mono_iff_injective _).mpr (restriction_injective R q E F)

#print axioms covering_of_closedFiber
#print axioms neighborhood_of_restriction_eq
#print axioms restriction_injective
#print axioms restriction_app_mono

end PrimeGap182.TypeIII.ProperLocalSectionsInjective
