import TypeIIIQSTCompactBridgeFromCompactifiedDerivedPushforward
import TypeIIIPublishedPrimitiveSources

/-!
# Both primitive dictionaries from the same Katz and Artin--Schreier constructions

The universal ordinary construction family is fixed before the prime. Katz
indices carry a nontrivial additive character, disjoint upper/lower lists of
multiplicative characters, positive rank, and the actual ordinary Tate twist.
They describe Katz's hypergeometric family, rather than all objects with the
same rank or lissity. Zero and middle extensions across zero are distinct.
The Artin--Schreier class contains only standard nontrivial additive-character
objects, not arbitrary polynomial pullbacks.

The ordinary primitive classes and bounded background classes are the SAME
construction's isomorphism closures. Background affine extensions are ordinary
H0 followed by the SAME ordinary extension and degree zero. Actual single/H0
comparison therefore proves both original dictionaries for EVERY class object.

The operations' realization as Katz's actual family (§8.2), actual ordinary
Tate twists and extensions, and continuous constructible Qbar2 sheaves remains
explicit general data. QST Proposition 7.8 bounds the genuine hypergeometric
class on Gm, and Proposition 7.5 bounds standard nontrivial Artin--Schreier
objects. This leaf introduces no complexity bound and no selected Kl3/AS
recognition premise. Existing primitive source laws must be applied on these
same constructed classes; traces on units alone do not identify extension at 0.

Primary sources: https://arxiv.org/html/2101.00635v4 (§7.3--7.4),
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf (§4.1, §11.0.1).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.QSTPrimitiveBridgesFromCommonKatzConstruction
open ExactInverseImagesToDerived CanonicalPrimeFramework StartingSourceComplexity
open QSTRealizationFromExactInverseImages
open QSTCompactBridgeFromCompactifiedDerivedPushforward

universe mu

/-- Multiplicative characters include the trivial character, as Katz allows. -/
abbrev MultiplicativeCharacter (K : Type) [Field K] := Kˣ →* (PadicAlgCl 2)ˣ

/-- Exact family indices; repeated characters within either list are allowed. -/
structure KatzIndex (K : Type) [Field K] where
  additive : AddChar K (PadicAlgCl 2)
  nontrivial : additive ≠ 1
  upper : List (MultiplicativeCharacter K)
  lower : List (MultiplicativeCharacter K)
  disjoint : ∀ χ, χ ∈ upper → χ ∈ lower → False
  positiveRank : 0 < max upper.length lower.length
  tateTwist : ℤ

def KatzIndex.rank {K : Type} [Field K] (a : KatzIndex K) : ℕ :=
  max a.upper.length a.lower.length

/-- The genuine Kloosterman indices: n trivial upper characters, no lower ones. -/
def kloostermanIndex {K : Type} [Field K] (ψ : AddChar K (PadicAlgCl 2))
    (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) (twist : ℤ) : KatzIndex K where
  additive := ψ
  nontrivial := hψ
  upper := List.replicate n 1
  lower := []
  disjoint := by simp
  positiveRank := by simpa using hn
  tateTwist := twist

theorem kloostermanIndex_rank {K : Type} [Field K] (ψ : AddChar K (PadicAlgCl 2))
    (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) (twist : ℤ) :
    (kloostermanIndex ψ hψ n hn twist).rank = n := by
  simp [KatzIndex.rank, kloostermanIndex]

variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)]
local instance localizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

/-- General genuine ordinary construction data, independent of the prime.
No target dictionary or complexity estimate occurs in this interface. -/
structure Constructions where
  katz : ∀ (K : Type) [Field K] [Fintype K], (2 : K) ≠ 0 →
    KatzIndex K → C (ArithmeticSourceMaps.fiberScheme K)
  tate : ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ℤ →
    C (ArithmeticSourceMaps.fiberScheme K) ⥤ C (ArithmeticSourceMaps.fiberScheme K)
  zero : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    C (ArithmeticSourceMaps.fiberScheme K) ⥤ C (StartingSourceMaps.affineLine K)
  middle : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    C (ArithmeticSourceMaps.fiberScheme K) ⥤ C (StartingSourceMaps.affineLine K)
  lineTate : ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ℤ →
    C (StartingSourceMaps.affineLine K) ⥤ C (StartingSourceMaps.affineLine K)
  zeroTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (n : ℤ),
    tate K h2 n ⋙ zero K h2 ≅ zero K h2 ⋙ lineTate K h2 n
  artinSchreier : ∀ (K : Type) [Field K] [Fintype K], (2 : K) ≠ 0 →
    AddChar K (PadicAlgCl 2) → C (StartingSourceMaps.affineLine K)

variable (O : Constructions C) (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)

/-- Apply the actual ordinary Tate operation, keeping the family normalization. -/
def member (a : KatzIndex K) : C (ArithmeticSourceMaps.fiberScheme K) :=
  (O.tate K h2 a.tateTwist).obj (O.katz K h2 { a with tateTwist := 0 })

/-- Arithmetic classes use actual zero or middle extensions of that family. -/
def primitiveClasses : PrimitiveClasses (C (StartingSourceMaps.affineLine K)) where
  Hypergeometric A r := ∃ a : KatzIndex K, a.rank = r ∧
    (Nonempty (A ≅ (O.zero K h2).obj (member C O K h2 a)) ∨
     Nonempty (A ≅ (O.middle K h2).obj (member C O K h2 a)))
  NontrivialArtinSchreier A := ∃ ψ : AddChar K (PadicAlgCl 2), ψ ≠ 1 ∧
    Nonempty (A ≅ O.artinSchreier K h2 ψ)

/-- The raw Kl3 object is the SAME Katz member extended by zero at zero. -/
def rawKloosterman3 (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    C (StartingSourceMaps.affineLine K) :=
  (O.zero K h2).obj (O.katz K h2 (kloostermanIndex ψ hψ 3 (by decide) 0))

def twistOne : C (StartingSourceMaps.affineLine K) ⥤ C (StartingSourceMaps.affineLine K) :=
  O.lineTate K h2 1

omit [∀ X, Abelian (C X)] in
/-- ALL nontrivial characters, with normalization from the actual Tate/zero law. -/
theorem normalizedKloosterman3_hypergeometric (ψ : AddChar K (PadicAlgCl 2))
    (hψ : ψ ≠ 1) : (primitiveClasses C O K h2).Hypergeometric
      ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) 3 := by
  refine ⟨kloostermanIndex ψ hψ 3 (by decide) 1,
    kloostermanIndex_rank ψ hψ 3 (by decide) 1, Or.inl ?_⟩
  exact ⟨((O.zeroTate K h2 1).app
    (O.katz K h2 (kloostermanIndex ψ hψ 3 (by decide) 0))).symm⟩

omit [∀ X, Abelian (C X)] in
theorem standardArtinSchreier_nontrivial (ψ : AddChar K (PadicAlgCl 2))
    (hψ : ψ ≠ 1) :
    (primitiveClasses C O K h2).NontrivialArtinSchreier (O.artinSchreier K h2 ψ) :=
  ⟨ψ, hψ, ⟨Iso.refl _⟩⟩

/-- The derived class is the SAME family in literal ordinary degree zero. -/
def hypergeometric (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) (r : ℕ) : Prop :=
  ∃ a : KatzIndex K, a.rank = r ∧
    Nonempty (A ≅ (boundedDegreeZero C _).obj (member C O K h2 a))

def nontrivialArtinSchreier (A : Bounded C (StartingSourceMaps.affineLine K)) : Prop :=
  ∃ ψ : AddChar K (PadicAlgCl 2), ψ ≠ 1 ∧
    Nonempty (A ≅ (boundedDegreeZero C _).obj (O.artinSchreier K h2 ψ))

/-- Ordinary extension is applied to actual H0; this is not derived middle extension. -/
def affineZero : Bounded C (ArithmeticSourceMaps.fiberScheme K) ⥤
    Bounded C (StartingSourceMaps.affineLine K) :=
  cohomology C _ 0 ⋙ O.zero K h2 ⋙ boundedDegreeZero C _

def affineMiddle : Bounded C (ArithmeticSourceMaps.fiberScheme K) ⥤
    Bounded C (StartingSourceMaps.affineLine K) :=
  cohomology C _ 0 ⋙ O.middle K h2 ⋙ boundedDegreeZero C _

/-- Actual standard single/H0 comparison, with no new compatibility law. -/
def singleH0Iso (X : Scheme.{0}) (A : C X) :
    (cohomology C X 0).obj ((boundedDegreeZero C X).obj A) ≅ A :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (C X) 0).app A

def zeroDegreeZeroIso (A : C (ArithmeticSourceMaps.fiberScheme K)) :
    (boundedDegreeZero C _).obj ((O.zero K h2).obj A) ≅
      (affineZero C O K h2).obj ((boundedDegreeZero C _).obj A) :=
  (boundedDegreeZero C _).mapIso ((O.zero K h2).mapIso (singleH0Iso C _ A).symm)

def middleDegreeZeroIso (A : C (ArithmeticSourceMaps.fiberScheme K)) :
    (boundedDegreeZero C _).obj ((O.middle K h2).obj A) ≅
      (affineMiddle C O K h2).obj ((boundedDegreeZero C _).obj A) :=
  (boundedDegreeZero C _).mapIso ((O.middle K h2).mapIso (singleH0Iso C _ A).symm)

/-- Exact original primitive dictionary, ALL objects of the constructed class. -/
theorem hypergeometricBridge (A : C (StartingSourceMaps.affineLine K)) (r : ℕ)
    (hA : (primitiveClasses C O K h2).Hypergeometric A r) :
    ∃ A0 : Bounded C (ArithmeticSourceMaps.fiberScheme K),
      hypergeometric C O K h2 A0 r ∧
        (Nonempty ((boundedDegreeZero C _).obj A ≅ (affineZero C O K h2).obj A0) ∨
         Nonempty ((boundedDegreeZero C _).obj A ≅ (affineMiddle C O K h2).obj A0)) := by
  obtain ⟨a, hr, hzero | hmiddle⟩ := hA
  · obtain ⟨e⟩ := hzero
    exact ⟨_, ⟨a, hr, ⟨Iso.refl _⟩⟩,
      Or.inl ⟨(boundedDegreeZero C _).mapIso e ≪≫ zeroDegreeZeroIso C O K h2 _⟩⟩
  · obtain ⟨e⟩ := hmiddle
    exact ⟨_, ⟨a, hr, ⟨Iso.refl _⟩⟩,
      Or.inr ⟨(boundedDegreeZero C _).mapIso e ≪≫ middleDegreeZeroIso C O K h2 _⟩⟩

/-- Exact standard AS dictionary; polynomial pullbacks are outside this class. -/
theorem artinSchreierBridge (A : C (StartingSourceMaps.affineLine K))
    (hA : (primitiveClasses C O K h2).NontrivialArtinSchreier A) :
    nontrivialArtinSchreier C O K h2 ((boundedDegreeZero C _).obj A) := by
  obtain ⟨ψ, hψ, ⟨e⟩⟩ := hA
  exact ⟨ψ, hψ, ⟨(boundedDegreeZero C _).mapIso e⟩⟩

section CanonicalQST
variable [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (g : X ⟶ Y), (U.pull g).Monoidal]
  (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{mu} (extensionObjects (primeSource C U p) (extraOrdinary C p) i) :=
  fun _ => HasDerivedCategory.standard _

def qstPrimitiveClasses : PrimitiveClasses ((primeSource C U p).Obj .line) :=
  primitiveClasses C O (ZMod p) hp2

/-- Exact Background.affineZero operation, with the same ordinary construction. -/
def qstAffineZero :
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm →
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line :=
  (affineZero C O (ZMod p) hp2).obj

def qstAffineMiddle :
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm →
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line :=
  (affineMiddle C O (ZMod p) hp2).obj

def qstHypergeometric :
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm →
    ℕ → Prop := hypergeometric C O (ZMod p) hp2

def qstNontrivialArtinSchreier :
    Obj (primeSource C U p) (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line →
    Prop := nontrivialArtinSchreier C O (ZMod p) hp2

/-- Exact original bridge types, without a supplied Background or SC dictionary. -/
theorem qstHypergeometricBridge (A : (primeSource C U p).Obj .line) (r : ℕ)
    (hA : (qstPrimitiveClasses C O U p hp2).Hypergeometric A r) :
    ∃ A0 : Obj (primeSource C U p)
        (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm,
      qstHypergeometric C O U p hp2 A0 r ∧
        (Nonempty ((degreeZero (primeSource C U p)
            (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line).obj A ≅
          qstAffineZero C O U p hp2 A0) ∨
         Nonempty ((degreeZero (primeSource C U p)
            (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line).obj A ≅
          qstAffineMiddle C O U p hp2 A0)) :=
  hypergeometricBridge C O (ZMod p) hp2 A r hA

theorem qstArtinSchreierBridge (A : (primeSource C U p).Obj .line)
    (hA : (qstPrimitiveClasses C O U p hp2).NontrivialArtinSchreier A) :
    qstNontrivialArtinSchreier C O U p hp2
      ((degreeZero (primeSource C U p)
        (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .line).obj A) :=
  artinSchreierBridge C O (ZMod p) hp2 A hA
end CanonicalQST

end PrimeGap182.TypeIII.QSTPrimitiveBridgesFromCommonKatzConstruction
