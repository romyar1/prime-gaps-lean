import TypeIIIHenselianEtaleScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Detection by the closed fiber over a local base

An open subset of the source of a proper morphism to Spec R, where
R is local, is the whole source if it contains the actual closed
fiber.  The proof only needs the weaker property that the morphism
is universally closed: a nonempty closed complement has closed
image, and that image contains the closed point of the local base.

The fiber in this file is the literal pullback along the residue
ring map.  Its actual projection has image precisely the inverse
image of the closed point.  No henselian assumption is required.

The same detection theorem proves uniqueness for maps into an
étale scheme: their equality locus is the inverse image of the
actual open diagonal.  Agreement on the closed-fiber pullback
makes this open locus the whole source.  Existence of extensions
from the closed fiber and proper base change are not asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.ProperLocalClosedFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open HenselianEtaleScheme

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The image of the actual residue morphism is exactly the closed point. -/
theorem residueSpec_range : Set.range (residueSpec R) = {closedPoint R} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change residueSpec R x = closedPoint R
    rw [Subsingleton.elim x (closedPoint (ResidueField R))]
    exact residueSpec_closedPoint R
  · intro hy
    have hy' : y = closedPoint R := hy
    exact ⟨closedPoint (ResidueField R), (residueSpec_closedPoint R).trans hy'.symm⟩

variable {X : Scheme.{u}} (q : X ⟶ Spec (.of R))

/-- The literal closed-fiber pullback along the actual residue morphism. -/
def closedFiber : Scheme.{u} := pullback q (residueSpec R)

/-- The actual first projection from this closed-fiber pullback. -/
def closedFiberι : closedFiber R q ⟶ X := pullback.fst q (residueSpec R)

/-- The image of that literal projection is precisely the closed-point fiber. -/
theorem closedFiberι_range :
    Set.range (closedFiberι R q) = q ⁻¹' {closedPoint R} := by
  change Set.range (pullback.fst q (residueSpec R)) = _
  rw [Scheme.Pullback.range_fst, residueSpec_range]

variable [UniversallyClosed q]

/-- Every nonempty closed subset of the source meets the closed fiber.
Only actual closedness of its image and localness of the base are used. -/
theorem closed_meets_closedFiber (C : Set X) (hC : IsClosed C) (hne : C.Nonempty) :
    ∃ x ∈ C, q x = closedPoint R := by
  obtain ⟨x, hx⟩ := hne
  have hclosed : IsClosed (q '' C) := q.isClosedMap C hC
  exact (specializes_closedPoint (q x)).mem_closed hclosed ⟨x, hx, rfl⟩

/-- An open containing the point-set closed fiber is the entire source. -/
theorem open_eq_top_of_preimage_closedPoint_subset (V : X.Opens)
    (hV : q ⁻¹' {closedPoint R} ⊆ (V : Set X)) : V = ⊤ := by
  classical
  apply top_le_iff.mp
  intro x _
  by_contra hx
  obtain ⟨y, hy, hqy⟩ := closed_meets_closedFiber R q (V : Set X)ᶜ
    V.2.isClosed_compl ⟨x, hx⟩
  exact hy (hV (show y ∈ q ⁻¹' {closedPoint R} from hqy))

/-- An open containing the image of the actual closed-fiber
pullback is all of X.  This applies in particular to every proper q. -/
theorem open_eq_top_of_closedFiber_subset (V : X.Opens)
    (hV : Set.range (closedFiberι R q) ⊆ (V : Set X)) : V = ⊤ := by
  apply open_eq_top_of_preimage_closedPoint_subset R q V
  rw [← closedFiberι_range]
  exact hV

/-- Two maps over the same base into an étale scheme agree globally
if they agree after the actual closed-fiber projection. -/
theorem maps_ext_of_closedFiber {Y Z : Scheme.{u}} (e : Y ⟶ Z) [Etale e]
    (s t : X ⟶ Y) (hbase : s ≫ e = t ≫ e)
    (hclosed : closedFiberι R q ≫ s = closedFiberι R q ≫ t) : s = t := by
  let F : X ⟶ pullback e e := pullback.lift s t hbase
  let V : X.Opens := F ⁻¹ᵁ (pullback.diagonal e).opensRange
  have hF : closedFiberι R q ≫ F =
      (closedFiberι R q ≫ s) ≫ pullback.diagonal e := by
    apply pullback.hom_ext
    · simp only [F, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · simpa only [F, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id] using hclosed.symm
  have hfiber : Set.range (closedFiberι R q) ⊆ (V : Set X) := by
    rintro _ ⟨z, rfl⟩
    change F (closedFiberι R q z) ∈ Set.range (pullback.diagonal e)
    refine ⟨s (closedFiberι R q z), ?_⟩
    have h := congrArg (fun f => f z) hF
    change F (closedFiberι R q z) =
      (pullback.diagonal e) (s (closedFiberι R q z)) at h
    exact h.symm
  have hV : V = ⊤ := open_eq_top_of_closedFiber_subset R q V hfiber
  have hRange : Set.range F ⊆ Set.range (pullback.diagonal e) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ V := by rw [hV]; trivial
    exact hx
  let l := IsOpenImmersion.lift (pullback.diagonal e) F hRange
  have hl : l ≫ pullback.diagonal e = F :=
    IsOpenImmersion.lift_fac (pullback.diagonal e) F hRange
  have hs : l = s := by
    have h := congrArg (fun f => f ≫ pullback.fst e e) hl
    simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      F, pullback.lift_fst] using h
  have ht : l = t := by
    have h := congrArg (fun f => f ≫ pullback.snd e e) hl
    simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
      F, pullback.lift_snd] using h
  exact hs.symm.trans ht

/-- Sections of any étale scheme over X are determined by their
restriction along the literal closed fiber of the proper local-base map. -/
theorem sections_ext_of_closedFiber {Y : Scheme.{u}} (e : Y ⟶ X) [Etale e]
    (s t : X ⟶ Y) (hs : s ≫ e = 𝟙 X) (ht : t ≫ e = 𝟙 X)
    (hclosed : closedFiberι R q ≫ s = closedFiberι R q ≫ t) : s = t :=
  maps_ext_of_closedFiber R q e s t (hs.trans ht.symm) hclosed

#print axioms residueSpec_range
#print axioms closedFiber
#print axioms closedFiberι
#print axioms closedFiberι_range
#print axioms closed_meets_closedFiber
#print axioms open_eq_top_of_preimage_closedPoint_subset
#print axioms open_eq_top_of_closedFiber_subset
#print axioms maps_ext_of_closedFiber
#print axioms sections_ext_of_closedFiber

end PrimeGap182.TypeIII.ProperLocalClosedFiber
