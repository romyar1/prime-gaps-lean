import TypeIIIProperLocalClosedFiber
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Finite étale isomorphisms detected on the actual closed fiber

Let X be proper over a local ring R and let e : Y ⟶ X be finite étale.
If the literal pullback of e along X₀ ⟶ X is an isomorphism, then e
is an isomorphism.  Monicity is detected by applying uniqueness on
the closed fiber to the two projections Y ×[X] Y ⟶ Y.  Surjectivity
follows because the open image contains the closed fiber of X.

Every fiber map below is the actual categorical pullback projection.
The proof requires neither henselianity nor extension of a section
or of a clopen subset from the closed fiber.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.ProperFiniteEtaleDetection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HenselianEtaleScheme ProperLocalClosedFiber

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable {X Y : Scheme.{u}} (q : X ⟶ Spec (.of R)) (e : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- Monicity of the literal base change of e forces two maps over X
to agree after their actual closed-fiber projection. -/
theorem closedFiber_comp_eq_of_mono_baseChange
    [Mono (pullback.snd e (closedFiberι R q))]
    {T : Scheme.{u}} (s t : T ⟶ Y) (h : s ≫ e = t ≫ e) :
    closedFiberι R (s ≫ e ≫ q) ≫ s = closedFiberι R (s ≫ e ≫ q) ≫ t := by
  let r := s ≫ e ≫ q
  let i := closedFiberι R r
  let k : closedFiber R r ⟶ closedFiber R q :=
    pullback.lift (i ≫ s ≫ e) (pullback.snd r (residueSpec R)) (by
      simpa only [i, closedFiberι, r, Category.assoc] using
        (pullback.condition (f := r) (g := residueSpec R)))
  let a : closedFiber R r ⟶ pullback e (closedFiberι R q) :=
    pullback.lift (i ≫ s) k (by
      simp only [k, closedFiberι, pullback.lift_fst, Category.assoc])
  let b : closedFiber R r ⟶ pullback e (closedFiberι R q) :=
    pullback.lift (i ≫ t) k (by
      simpa only [k, closedFiberι, pullback.lift_fst, Category.assoc] using
        congrArg (fun f => i ≫ f) h.symm)
  have hab : a = b := (cancel_mono (pullback.snd e (closedFiberι R q))).mp (by
    simp only [a, b, pullback.lift_snd])
  have hab' := congrArg (fun f => f ≫ pullback.fst e (closedFiberι R q)) hab
  simpa only [a, b, pullback.lift_fst, i, r] using hab'

/-- A finite étale morphism over a proper local-base scheme is monic
if its literal closed-fiber base change is monic. -/
theorem mono_of_mono_closedFiber [IsProper q] [IsFinite e] [Etale e]
    [Mono (pullback.snd e (closedFiberι R q))] : Mono e := by
  have hp : pullback.fst e e = pullback.snd e e :=
    maps_ext_of_closedFiber R (pullback.fst e e ≫ e ≫ q) e
      (pullback.fst e e) (pullback.snd e e) pullback.condition
      (closedFiber_comp_eq_of_mono_baseChange R q e
        (pullback.fst e e) (pullback.snd e e) pullback.condition)
  constructor
  intro T s t h
  calc
    s = pullback.lift s t h ≫ pullback.fst e e := (pullback.lift_fst ..).symm
    _ = pullback.lift s t h ≫ pullback.snd e e := congrArg (fun f => pullback.lift s t h ≫ f) hp
    _ = t := pullback.lift_snd ..

/-- Surjectivity of the actual closed-fiber base change detects
surjectivity of an étale map.  Universal closedness of q suffices. -/
theorem surjective_of_surjective_closedFiber [UniversallyClosed q] [Etale e]
    [Surjective (pullback.snd e (closedFiberι R q))] : Surjective e := by
  let V : X.Opens := ⟨Set.range e, e.isOpenMap.isOpen_range⟩
  have hV : V = ⊤ := open_eq_top_of_closedFiber_subset R q V (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := (pullback.snd e (closedFiberι R q)).surjective z
    refine ⟨pullback.fst e (closedFiberι R q) w, ?_⟩
    have hc := congrArg (fun f => f w)
      (pullback.condition (f := e) (g := closedFiberι R q))
    change e (pullback.fst e (closedFiberι R q) w) =
      closedFiberι R q (pullback.snd e (closedFiberι R q) w) at hc
    exact hc.trans (congrArg (closedFiberι R q) hw))
  constructor
  intro x
  have hx : x ∈ V := by rw [hV]; trivial
  exact hx

/-- The literal closed-fiber pullback detects isomorphisms among
finite étale maps over a proper scheme over a local ring. -/
theorem isIso_of_closedFiber [IsProper q] [IsFinite e] [Etale e]
    [IsIso (pullback.snd e (closedFiberι R q))] : IsIso e := by
  let : Mono e := mono_of_mono_closedFiber R q e
  let : Surjective e := surjective_of_surjective_closedFiber R q e
  exact Flat.isIso_of_surjective_of_mono e

/-- The isomorphism criterion uses the unchanged categorical
base-change map in both directions. -/
theorem isIso_iff_closedFiber [IsProper q] [IsFinite e] [Etale e] :
    IsIso e ↔ IsIso (pullback.snd e (closedFiberι R q)) := by
  constructor
  · intro h
    let : IsIso e := h
    infer_instance
  · intro h
    let : IsIso (pullback.snd e (closedFiberι R q)) := h
    exact isIso_of_closedFiber R q e

#print axioms closedFiber_comp_eq_of_mono_baseChange
#print axioms mono_of_mono_closedFiber
#print axioms surjective_of_surjective_closedFiber
#print axioms isIso_of_closedFiber
#print axioms isIso_iff_closedFiber

end PrimeGap182.TypeIII.ProperFiniteEtaleDetection
