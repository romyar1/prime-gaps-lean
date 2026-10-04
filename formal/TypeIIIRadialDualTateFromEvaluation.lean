import TypeIIITensorListRepresentation
import TypeIIICompactPairingFromCupTrace

/-!
# Geometric-inertia dual/Tate from the original evaluation

The inverse-image and inertia functors are indexed over all actual maps of
the fixed source and target schemes. The same ordinary evaluation line is
trivialized on geometric inertia, through the same functor's unit comparison.
For lisse objects the ordinary internal-Hom stalk comparison realizes that
exact evaluation, in the order V tensor DT(V). Its equivariance is derived
from the resulting FDRep morphism, rather than supplied as a dual-action law.

The geometric realization of these functors, the trace-line trivialization,
and the lisse internal-Hom comparison remain general framework parameters.
In particular this module does not provide a common geometric realization,
an arithmetic Frobenius law, or a claim that arbitrary constructible objects
have perfect ordinary-dual stalks.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped MonoidalCategory TensorProduct

namespace PrimeGap182.TypeIII.RadialDualTateFromEvaluation
open PublishedPhaseApplication

universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type w} [Group G] {S T : Scheme}
  (F : (S ⟶ T) → C ⥤ FDRep ℂ G)
  (DT : Cᵒᵖ ⥤ C) (Lisse : C → Prop)
  (ev : CompactPairingFromCupTrace.Evaluation DT Lisse)

/-- The actual evaluation morphism after the same tensor, trace-line, and
unit comparisons. The trace line is the original evaluation line. -/
def pairingMorphism (f : S ⟶ T) (M : (F f).Monoidal)
    (line : (F f).obj ev.line ≅ (F f).obj (𝟙_ C)) (V : C) :
    (F f).obj V ⊗ (F f).obj (DT.obj (op V)) ⟶ 𝟙_ (FDRep ℂ G) := by
  letI := M
  exact (Functor.Monoidal.μIso (F f) V (DT.obj (op V))).hom ≫
    (F f).map (ev.evaluate V) ≫ line.hom ≫ (Functor.Monoidal.εIso (F f)).inv

/-- The scalar pairing is the same FDRep evaluation on a pure tensor. -/
def pairing (f : S ⟶ T) (M : (F f).Monoidal)
    (line : (F f).obj ev.line ≅ (F f).obj (𝟙_ C)) (V : C)
    (u : (F f).obj V) (v : (F f).obj (DT.obj (op V))) : ℂ :=
  (pairingMorphism F DT Lisse ev f M line V).hom.hom (u ⊗ₜ[ℂ] v)

/-- General geometric inverse-image/inertia realization. Only the SAME
trace line has an equivariant trivialization; the dual comparison is merely
linear, with no action-compatibility premise. Perfection is lisse-guarded. -/
structure Comparison where
  [monoidal : ∀ f, (F f).Monoidal]
  line : ∀ f, (F f).obj ev.line ≅ (F f).obj (𝟙_ C)
  equiv : ∀ f V, Lisse V → (F f).obj (DT.obj (op V)) ≃ₗ[ℂ]
    Module.Dual ℂ ((F f).obj V)
  evaluation : ∀ f V (hV : Lisse V) u v,
    equiv f V hV v u = pairing F DT Lisse ev f (monoidal f) (line f) V u v


variable {F DT Lisse ev}

/-- An FDRep morphism into the tensor unit gives invariant evaluation on
every geometric-inertia element, without a dual-action premise. -/
theorem pairing_invariant (P : Comparison F DT Lisse ev)
    (f : S ⟶ T) (V : C) (g : G)
    (u : (F f).obj V) (v : (F f).obj (DT.obj (op V))) :
    pairing F DT Lisse ev f (P.monoidal f) (P.line f) V
      (((F f).obj V).ρ g u) (((F f).obj (DT.obj (op V))).ρ g v) =
      pairing F DT Lisse ev f (P.monoidal f) (P.line f) V u v := by
  have h := congrArg (fun m => m.hom.hom (u ⊗ₜ[ℂ] v))
    ((pairingMorphism F DT Lisse ev f (P.monoidal f) (P.line f) V).comm g)
  change pairing F DT Lisse ev f (P.monoidal f) (P.line f) V
      (((F f).obj V).ρ g u) (((F f).obj (DT.obj (op V))).ρ g v) =
    pairing F DT Lisse ev f (P.monoidal f) (P.line f) V u v at h
  exact h

/-- The lisse dual-stalk comparison intertwines the inverse action on its
argument, forced by the original evaluation pairing. -/
theorem contragredient (P : Comparison F DT Lisse ev)
    (f : S ⟶ T) (V : C) (hV : Lisse V) (g : G)
    (v : (F f).obj (DT.obj (op V))) (u : (F f).obj V) :
    P.equiv f V hV (((F f).obj (DT.obj (op V))).ρ g v) u =
      P.equiv f V hV v (((F f).obj V).ρ g⁻¹ u) := by
  rw [P.evaluation, P.evaluation]
  have h := pairing_invariant P f V g (((F f).obj V).ρ g⁻¹ u) v
  rw [Representation.self_inv_apply] at h
  exact h

/-- The old radial dual/Tate representation equivalence is derived from
the same evaluation, for every actual map and every lisse source object. -/
def dualTateEquiv (P : Comparison F DT Lisse ev)
    (f : S ⟶ T) (V : C) (hV : Lisse V) :
    Representation.Equiv ((F f).obj (DT.obj (op V))).ρ
      (dualRepresentation ((F f).obj V)).ρ where
  toLinearEquiv := P.equiv f V hV
  isIntertwining' g := by
    ext v
    apply LinearMap.ext
    intro u
    exact contragredient P f V hV g v u

end PrimeGap182.TypeIII.RadialDualTateFromEvaluation

#print axioms PrimeGap182.TypeIII.RadialDualTateFromEvaluation.pairingMorphism
#print axioms PrimeGap182.TypeIII.RadialDualTateFromEvaluation.pairing
#print axioms PrimeGap182.TypeIII.RadialDualTateFromEvaluation.pairing_invariant
#print axioms PrimeGap182.TypeIII.RadialDualTateFromEvaluation.contragredient
#print axioms PrimeGap182.TypeIII.RadialDualTateFromEvaluation.dualTateEquiv
