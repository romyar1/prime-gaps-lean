import TypeIIIOriginFiniteConstantInvariantFrobeniusTransport04

/-!
Independently standard finite-constant Gm/trait operations, with the GENERAL
published comparison stated separately from their interpretation. The prescribed
interpretation reads only S/B/X: continuous constructible Qbar2 coefficients,
Gm_E -> Gm_K from the SAME finite-field Algebra K E, compatible positive-T
pointed traits, their geometric inertia/Weil maps, chosen GEOMETRIC Frobenius
lifts, and the SAME fixed scalar embedding into C. It must not read native
C/U/F, an OriginStalks result, a source sheaf, or a completed formula.

The finite-constant nearby theorem is a functorial coefficient comparison.
Its ALL-Weil square and lift image follow the genuine arithmetic geometry,
not arbitrary LocalWeilAction.Data. No model existence or exact native theorem
interpretation is proved. The published shape is a corollary/application of
finite-etale constant change and the local inertia exact sequence, not a
verbatim theorem with this Lean signature.
-/
noncomputable section
open CategoryTheory
namespace PrimeGap182.TypeIII.StandardFiniteConstantOrigin
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open OriginStalksFromStandardWeilInvariants
universe nu

/-- Primitive standard geometric maps only; no coefficient, invariant-stalk,
Frobenius-power, or completed origin comparison is supplied by this record. -/
structure Operations (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S) where
  curvePull : ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
    (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0), S.Curve K h2K ⥤ S.Curve E h2E
  inertia : ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
    (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0), B.OriginGroup E h2E ≃* B.OriginGroup K h2K
  weilMap : ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
    (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0),
    (B.originWeil E h2E).Weil →* (B.originWeil K h2K).Weil

/-- GENERAL theorems over every interpreted independent package and every
finite constant extension. Model/primitive existence is not a theorem field. -/
structure PublishedTheorems
    (interpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
      Operations S B → Prop) : Prop where
  nearby : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S) (X : Operations S B),
    interpretation S B X → ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
      (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0),
      ∃ nearby : X.curvePull K E h2K h2E ⋙ B.origin E h2E ≅
        B.origin K h2K ⋙ Action.res (FGModuleCat ℂ) (X.inertia K E h2K h2E).toMonoidHom,
        ∀ A w x, (nearby.hom.app A).hom.hom
          ((B.originWeil E h2E).representation ((X.curvePull K E h2K h2E).obj A) w x) =
        (B.originWeil K h2K).representation A (X.weilMap K E h2K h2E w)
          ((nearby.hom.app A).hom.hom x)
  inertia : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S) (X : Operations S B),
    interpretation S B X → ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
      (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0) q,
      X.weilMap K E h2K h2E ((B.originWeil E h2E).inertia q) =
        (B.originWeil K h2K).inertia (X.inertia K E h2K h2E q)
  frobeniusImage : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S)
    (X : Operations S B), interpretation S B X →
    ∀ (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
      (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0),
      ∃ q : B.OriginGroup K h2K,
        X.weilMap K E h2K h2E (B.originWeil E h2E).frobenius =
          (B.originWeil K h2K).inertia q *
            (B.originWeil K h2K).frobenius ^ Module.finrank K E

variable {interpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    Operations S B → Prop}
  (published : PublishedTheorems interpretation)
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S) (X : Operations S B)
  (model : interpretation S B X)
  (K E : Type) [Field K] [Field E] [Fintype K] [Fintype E] [Algebra K E]
  (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0)

/-- Choose only the individual nearby coefficient NatIso from GENERAL. -/
def nearbyIso : X.curvePull K E h2K h2E ⋙ B.origin E h2E ≅
    B.origin K h2K ⋙ Action.res (FGModuleCat ℂ) (X.inertia K E h2K h2E).toMonoidHom :=
  Classical.choose (published.nearby S B X model K E h2K h2E)

theorem nearbyIso_weil (A : S.Curve K h2K) (w : (B.originWeil E h2E).Weil)
    (x : ((B.origin E h2E).obj ((X.curvePull K E h2K h2E).obj A)).V) :
    ((nearbyIso published B X model K E h2K h2E).hom.app A).hom.hom
      ((B.originWeil E h2E).representation ((X.curvePull K E h2K h2E).obj A) w x) =
    (B.originWeil K h2K).representation A (X.weilMap K E h2K h2E w)
      (((nearbyIso published B X model K E h2K h2E).hom.app A).hom.hom x) :=
  Classical.choose_spec (published.nearby S B X model K E h2K h2E) A w x

/-- The invariant-stalk comparison is a computed output, not MODEL/GENERAL. -/
def invariantComparison (A : S.Curve K h2K) :
    (invariantStalks (B.origin E h2E) (B.originConjugation E h2E) (B.originWeil E h2E)).fiber
      ((X.curvePull K E h2K h2E).obj A) ≃ₗ[ℂ]
    (invariantStalks (B.origin K h2K) (B.originConjugation K h2K) (B.originWeil K h2K)).fiber A :=
  OriginFiniteConstantInvariantFrobeniusTransport.comparison (X.curvePull K E h2K h2E)
    (B.origin K h2K) (B.origin E h2E) (B.originConjugation K h2K) (B.originConjugation E h2E)
    (B.originWeil K h2K) (B.originWeil E h2E) (X.inertia K E h2K h2E)
    (nearbyIso published B X model K E h2K h2E) A

/-- ALL ordinary standard objects and the SAME finite-field degree. -/
theorem invariant_frobenius_square (A : S.Curve K h2K)
    (x : (invariantStalks (B.origin E h2E) (B.originConjugation E h2E) (B.originWeil E h2E)).fiber
      ((X.curvePull K E h2K h2E).obj A)) :
    invariantComparison published B X model K E h2K h2E A
      ((invariantStalks (B.origin E h2E) (B.originConjugation E h2E)
        (B.originWeil E h2E)).frobenius ((X.curvePull K E h2K h2E).obj A) x) =
    ((invariantStalks (B.origin K h2K) (B.originConjugation K h2K)
      (B.originWeil K h2K)).frobenius A ^ Module.finrank K E)
      (invariantComparison published B X model K E h2K h2E A x) := by
  obtain ⟨q, hq⟩ := published.frobeniusImage S B X model K E h2K h2E
  exact OriginFiniteConstantInvariantFrobeniusTransport.comparison_frobenius_pow
    (X.curvePull K E h2K h2E) (B.origin K h2K) (B.origin E h2E)
    (B.originConjugation K h2K) (B.originConjugation E h2E)
    (B.originWeil K h2K) (B.originWeil E h2E) (X.inertia K E h2K h2E)
    (nearbyIso published B X model K E h2K h2E) (X.weilMap K E h2K h2E)
    (nearbyIso_weil published B X model K E h2K h2E) A (Module.finrank K E) q hq x
end PrimeGap182.TypeIII.StandardFiniteConstantOrigin
