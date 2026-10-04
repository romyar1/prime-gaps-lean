import TypeIIIQSTDualityBridgesFromSmoothLisseVerdier
import TypeIIICompactPairingFromCupTrace
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Canonical ordinary dual and dual/Tate evaluation

All ordinary closed braided coefficient categories are fixed before the prime.
The source evaluation is the actual closed evaluation into the ordinary unit,
with braiding to put the dual first. The parameter evaluation has the exact
line(-1) tensor order of ordinaryDualTateMinusOne and the same line(-1) target.

The only general law used for separation is the finite-locally-free tensor/Hom
isomorphism: for EVERY scheme, EVERY coefficient line and EVERY globally lisse
finite-rank ordinary object, the COMPUTED curried evaluation is an isomorphism.
Global lissity here must realize finite-rank adic local systems in the actual
coefficient model. No selected evaluation normalization, completed Evaluation,
point Frobenius, trace, purity or stalk comparison is a premise of this leaf.
The ordinary/continuous-adic realization of the general law remains external.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalOrdinaryDualEvaluation
open ExactInverseImagesToDerived CanonicalPrimeFramework
open QSTDualityBridgesFromSmoothLisseVerdier

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, MonoidalCategory (C X)]
  [∀ X, MonoidalClosed (C X)] [∀ X, BraidedCategory (C X)]

/-- The original source order dual(V) tensor V, with the actual unit target. -/
def sourceEvaluate (X : Scheme) (V : C X) :
    (ordinaryDual C X).obj (Opposite.op V) ⊗ V ⟶ 𝟙_ (C X) :=
  (β_ _ _).hom ≫ (ihom.ev V).app (𝟙_ (C X))

/-- Contravariant closed evaluation naturality, in the original source order. -/
theorem sourceEvaluate_natural (X : Scheme) {V W : C X} (f : V ⟶ W) :
    ((ordinaryDual C X).map f.op ⊗ₘ 𝟙 V) ≫ sourceEvaluate C X V =
      (𝟙 ((ordinaryDual C X).obj (Opposite.op W)) ⊗ₘ f) ≫ sourceEvaluate C X W := by
  change (((MonoidalClosed.pre f).app (𝟙_ (C X))) ⊗ₘ 𝟙 V) ≫
      (β_ _ _).hom ≫ (ihom.ev V).app (𝟙_ (C X)) =
    (𝟙 ((ihom W).obj (𝟙_ (C X))) ⊗ₘ f) ≫
      (β_ _ _).hom ≫ (ihom.ev W).app (𝟙_ (C X))
  simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
  rw [BraidedCategory.braiding_naturality_right_assoc]

/-- Actual line tensor evaluation in the order (line tensor dual(V)) tensor V. -/
def linePairing (X : Scheme) (line V : C X) :
    (line ⊗ (ordinaryDual C X).obj (Opposite.op V)) ⊗ V ⟶ line :=
  (α_ _ _ _).hom ≫ line ◁ sourceEvaluate C X V ≫ (ρ_ line).hom

theorem linePairing_natural (X : Scheme) (line : C X) {V W : C X} (f : V ⟶ W) :
    ((line ◁ (ordinaryDual C X).map f.op) ⊗ₘ 𝟙 V) ≫ linePairing C X line V =
      (𝟙 (line ⊗ (ordinaryDual C X).obj (Opposite.op W)) ⊗ₘ f) ≫
        linePairing C X line W := by
  calc
    _ = (α_ line ((ordinaryDual C X).obj (Opposite.op W)) V).hom ≫
        line ◁ (((ordinaryDual C X).map f.op ⊗ₘ 𝟙 V) ≫ sourceEvaluate C X V) ≫
        (ρ_ line).hom := by
      rw [linePairing, MonoidalCategory.whiskerLeft_comp]
      have hn := MonoidalCategory.associator_naturality
        (𝟙 line) ((ordinaryDual C X).map f.op) (𝟙 V)
      simp only [MonoidalCategory.id_tensorHom] at hn
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ line ◁ sourceEvaluate C X V ≫ (ρ_ line).hom) hn
    _ = (α_ line ((ordinaryDual C X).obj (Opposite.op W)) V).hom ≫
        line ◁ ((𝟙 ((ordinaryDual C X).obj (Opposite.op W)) ⊗ₘ f) ≫ sourceEvaluate C X W) ≫
        (ρ_ line).hom := by rw [sourceEvaluate_natural]
    _ = _ := by
      rw [linePairing, MonoidalCategory.whiskerLeft_comp]
      have hn := MonoidalCategory.associator_naturality
        (𝟙 line) (𝟙 ((ordinaryDual C X).obj (Opposite.op W))) f
      rw [MonoidalCategory.id_tensorHom_id] at hn
      simp only [MonoidalCategory.id_tensorHom] at hn
      simpa only [Category.assoc, MonoidalCategory.id_tensorHom] using
        congrArg (fun k => k ≫ line ◁ sourceEvaluate C X W ≫ (ρ_ line).hom) hn.symm

/-- Evaluation in the parameter record's order V tensor (line tensor dual(V)). -/
def evaluateLine (X : Scheme) (line V : C X) :
    V ⊗ (line ⊗ (ordinaryDual C X).obj (Opposite.op V)) ⟶ line :=
  (β_ _ _).hom ≫ linePairing C X line V

theorem evaluateLine_natural (X : Scheme) (line : C X) {V W : C X} (f : V ⟶ W) :
    (f ⊗ₘ 𝟙 (line ⊗ (ordinaryDual C X).obj (Opposite.op W))) ≫ evaluateLine C X line W =
      (𝟙 V ⊗ₘ (line ◁ (ordinaryDual C X).map f.op)) ≫ evaluateLine C X line V := by
  simp only [evaluateLine, MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  rw [BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_right_assoc]
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    congrArg (fun k => (β_ V (line ⊗ (ordinaryDual C X).obj (Opposite.op W))).hom ≫ k)
      (linePairing_natural C X line f).symm

/-- Computed tensor/internal-Hom comparison; it is not supplied as a morphism. -/
def tensorHomComparison (X : Scheme) (line V : C X) :
    line ⊗ (ordinaryDual C X).obj (Opposite.op V) ⟶ (ihom V).obj line :=
  MonoidalClosed.curry (evaluateLine C X line V)

theorem evaluateLine_separates (X : Scheme) (line V U : C X)
    [IsIso (tensorHomComparison C X line V)]
    (f g : U ⟶ line ⊗ (ordinaryDual C X).obj (Opposite.op V))
    (h : (𝟙 V ⊗ₘ f) ≫ evaluateLine C X line V =
      (𝟙 V ⊗ₘ g) ≫ evaluateLine C X line V) : f = g := by
  apply (cancel_mono (tensorHomComparison C X line V)).1
  have hc := congrArg MonoidalClosed.curry h
  simpa only [tensorHomComparison, MonoidalCategory.id_tensorHom,
    MonoidalClosed.curry_natural_left] using hc

/-- General line evaluation record: all four old fields are constructed. -/
def evaluation (X : Scheme) (line : C X) (Lisse : C X → Prop)
    (tensorHomIsIso : ∀ V, Lisse V → IsIso (tensorHomComparison C X line V)) :
    CompactPairingFromCupTrace.Evaluation
      (ordinaryDual C X ⋙ MonoidalCategory.tensorLeft line) Lisse where
  line := line
  evaluate := evaluateLine C X line
  natural := evaluateLine_natural C X line
  separates := by
    intro V hV U f g h
    let := tensorHomIsIso V hV
    exact evaluateLine_separates C X line V U f g h

variable [∀ X, Abelian (C X)]
  (O : QSTDualityBridgesFromSmoothLisseVerdier.Operations C)
  (tensorHomIsIso : ∀ (X : Scheme) (line V : C X), O.globalLisse X V →
    IsIso (tensorHomComparison C X line V))

/-- ALL schemes and ALL integer Tate lines, before prime selection. -/
def tateEvaluation (X : Scheme) (n : ℤ) :
    CompactPairingFromCupTrace.Evaluation
      (ordinaryDual C X ⋙ ordinaryTate C O X n) (O.globalLisse X) :=
  evaluation C X (O.line X n) (O.globalLisse X)
    (fun V hV => tensorHomIsIso X (O.line X n) V hV)

section CanonicalPrime
variable (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (p : ℕ) [Fact p.Prime]

/-- Exact Root sourceEvaluation type, computed at the original global source. -/
def sourceEvaluation : ∀ A : (primeSource C U p).Obj .source,
    (sourceDualFunctor C U p).obj (Opposite.op A) ⊗ A ⟶ 𝟙_ ((primeSource C U p).Obj .source) :=
  sourceEvaluate C (StartingSourceMaps.sourceScheme (ZMod p))

/-- Exact Root parameterEvaluation0, with SAME line(-1) and global lissity. -/
def parameterEvaluation0 : CompactPairingFromCupTrace.Evaluation
    (torusDualTateFunctor C O U p)
    (O.globalLisse (PhysicalTorusMorphism.torusScheme (ZMod p))) :=
  tateEvaluation C O tensorHomIsIso (PhysicalTorusMorphism.torusScheme (ZMod p)) (-1)

end CanonicalPrime
end PrimeGap182.TypeIII.CanonicalOrdinaryDualEvaluation
