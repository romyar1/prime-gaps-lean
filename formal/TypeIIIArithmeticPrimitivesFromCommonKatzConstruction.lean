import TypeIIIQSTPrimitiveBridgesFromCommonKatzConstruction
import TypeIIIRationalPointStalks

/-!
# Arithmetic primitive operations from the same ordinary constructions

The Artin--Schreier and Tate operations are the original construction's
operations, including at the trivial additive character. The raw rank-three
Kloosterman operation is its actual zero extension for every nontrivial
character. Its otherwise unused trivial-character branch is the zero object;
no genuine Kloosterman or trace assertion is made about that branch.

The two original class-membership laws follow from the existing normalized
Kloosterman and standard Artin--Schreier membership theorems. The five other
original primitive laws remain separately curried with their exact guards.
No new mathematical premise or independent primitive operation is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

namespace PrimeGap182.TypeIII.ArithmeticPrimitivesFromCommonKatzConstruction
open ExactInverseImagesToDerived CanonicalPrimeFramework StartingSourceComplexity CanonicalCurveInput
open QSTPrimitiveBridgesFromCommonKatzConstruction

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)] (O : Constructions C)

/-- Total interface; only the nontrivial-character branch is genuine raw Kl3. -/
def kloosterman3 (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) : C (StartingSourceMaps.affineLine K) :=
  if hψ : ψ ≠ 1 then rawKloosterman3 C O K h2 ψ hψ else 0

theorem kloosterman3_nontrivial (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    kloosterman3 C O K h2 ψ = rawKloosterman3 C O K h2 ψ hψ := by
  simp only [kloosterman3, dite_eq_left hψ]

theorem kloosterman3_trivial (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) : kloosterman3 C O K h2 1 = 0 := by
  simp only [kloosterman3, ne_eq, not_true_eq_false, dite_eq_right, not_false_eq_true]

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)

/-- The original three-field arithmetic interface, with no separate choices. -/
def primitiveOperations :
    RationalPointStalks.PrimitiveOperations p (C (StartingSourceMaps.affineLine (ZMod p))) where
  artinSchreier := O.artinSchreier (ZMod p) h2
  kloosterman3 := kloosterman3 C O (ZMod p) h2
  twistOne := (O.lineTate (ZMod p) h2 1).obj

theorem primitiveOperations_artinSchreier :
    (primitiveOperations C O p h2).artinSchreier = O.artinSchreier (ZMod p) h2 := rfl

theorem primitiveOperations_twistOne :
    (primitiveOperations C O p h2).twistOne = (O.lineTate (ZMod p) h2 1).obj := rfl

theorem primitiveOperations_kloosterman3_nontrivial
    (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    (primitiveOperations C O p h2).kloosterman3 ψ =
      rawKloosterman3 C O (ZMod p) h2 ψ hψ :=
  kloosterman3_nontrivial C O (ZMod p) h2 ψ hψ

theorem primitiveOperations_kloosterman3_trivial :
    (primitiveOperations C O p h2).kloosterman3 1 = 0 :=
  kloosterman3_trivial C O (ZMod p) h2

/-- Exact old hypergeometric clause, for ALL nontrivial characters. -/
theorem hypergeometric (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    (primitiveClasses C O (ZMod p) h2).Hypergeometric
      ((primitiveOperations C O p h2).twistOne
        ((primitiveOperations C O p h2).kloosterman3 ψ)) 3 := by
  rw [primitiveOperations_kloosterman3_nontrivial C O p h2 ψ hψ]
  exact normalizedKloosterman3_hypergeometric C O (ZMod p) h2 ψ hψ

/-- Exact old standard AS clause, for ALL nontrivial characters. -/
theorem nontrivialAS (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    (primitiveClasses C O (ZMod p) h2).NontrivialArtinSchreier
      ((primitiveOperations C O p h2).artinSchreier ψ) :=
  standardArtinSchreier_nontrivial C O (ZMod p) h2 ψ hψ

section OriginalArithmetic
variable [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (R : RationalPointStalks.Data (primeSource C U p))

local notation "D" => RationalPointStalks.PrimitiveOperations.primitive R
  (primitiveOperations C O p h2)

/-- The literal original canonical raw object is the genuine SAME-O raw Kl3. -/
theorem canonical_rawKl : (D).rawKl =
    rawKloosterman3 C O (ZMod p) h2 (CanonicalSourceCharacter.prime p)
      (CanonicalSourceCharacter.prime_ne_one p) :=
  primitiveOperations_kloosterman3_nontrivial C O p h2 _
    (CanonicalSourceCharacter.prime_ne_one p)

theorem canonical_as : (D).as = O.artinSchreier (ZMod p) h2
    (CanonicalSourceCharacter.prime p) := rfl

theorem canonical_twistOne : (D).twistOne = (O.lineTate (ZMod p) h2 1).obj := rfl

theorem canonical_hypergeometric :
    (qstPrimitiveClasses C O U p h2).Hypergeometric ((D).twistOne (D).rawKl) 3 :=
  hypergeometric C O p h2 _ (CanonicalSourceCharacter.prime_ne_one p)

theorem canonical_nontrivialAS :
    (qstPrimitiveClasses C O U p h2).NontrivialArtinSchreier (D).as :=
  nontrivialAS C O p h2 _ (CanonicalSourceCharacter.prime_ne_one p)

variable (LG : LineGeometry ((primeSource C U p).Obj .line))

/-- Retain the five original clauses individually; construct the full old
seven-field Rules on the SAME operations, stalk traces and primitive classes. -/
theorem rulesConstructor
    (kl3 : 3 < p → ∀ ψ, ψ ≠ 1 →
      Kl3Properties LG ((D).twistOne ((D).kloosterman3 ψ)))
    (artinSchreier : 3 < p → ∀ ψ, ψ ≠ 1 →
      ASProperties LG ((D).artinSchreier ψ))
    (rawTrace : ∀ ψ, ψ ≠ 1 →
      ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ z : Eˣ,
        (D).trace E ((D).kloosterman3 ψ) (z : E) =
          (-1 : ℂ) ^ (3 - 1) * KatzSourceNormalization.rawKl3
            (PublishedPrimitiveSources.complexCharacter p ψ E) z)
    (tateTrace : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ A z,
      (D).trace E ((D).twistOne A) z =
        (Fintype.card E : ℂ)⁻¹ * (D).trace E A z)
    (asTrace : ∀ ψ, ψ ≠ 1 →
      ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E], ∀ z : E,
        (D).trace E ((D).artinSchreier ψ) z =
          TwoAdicComplexEmbedding.complexEquiv (PublishedPrimitiveSources.extension p ψ E z)) :
    PublishedPrimitiveSources.Rules D LG (qstPrimitiveClasses C O U p h2) where
  kl3 := kl3
  artinSchreier := artinSchreier
  hypergeometric := hypergeometric C O p h2
  nontrivialAS := nontrivialAS C O p h2
  rawTrace := rawTrace
  tateTrace := tateTrace
  asTrace := asTrace
end OriginalArithmetic

end PrimeGap182.TypeIII.ArithmeticPrimitivesFromCommonKatzConstruction
