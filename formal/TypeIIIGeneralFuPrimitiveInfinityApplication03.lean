import TypeIIIPublishedLocalInfinity
import TypeIIIOriginModelsFromSameComputedCoefficients

/-!
# Fu's GENERAL primitive infinity theorem applied on one ordinary theory

The premise covers ALL positive ranks n<p, ALL nontrivial characters over
finite base fields, and ALL algebraically closed extension fields. The
quadratic Kummer factor with exponent n-1 is retained. Its even-power
identity is an ALL-object geometric operation law. At n=3 the exponent
is two; the normalized Tate twist is removed only on geometric inertia.

The local raw object is the literal same-U pull of same-O zero extension
of the rank-n Katz construction. No selected raw model, normalized model
or KloostermanInfinityRules is an input. CubicCoverData is constructed
from the n=3 instance of the GENERAL power-cover operations, without a
recognition equality between independently chosen cover functors.

Genuine continuous-adic realization and identification of these GENERAL
operations with Fu Proposition0.8 remain external published premises.
This application neither constructs those foundations nor proves TypeIII.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.GeneralFuPrimitiveInfinityApplication03

open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open PublishedPhaseApplication PublishedMackey StartingSourceMaps
open ArithmeticSourceMaps CanonicalLocalCorrelation
open scoped TwoAdicComplexEmbedding

universe mu v w

/-- The actual finite power-cover operations; theorem applications below
require n>0 and n<p. This declaration adds no cover identity theorem. -/
structure PowerCoverData (n : ℕ) (E : Type) [Field E]
    (I : Type) [Group I] (H : Type v) [Group H] where
  push : RepresentationFunctor ℂ H I
  pull : RepresentationFunctor ℂ I H
  deck : Fin n → RepresentationFunctor ℂ H H
  zeta : Fin n → E
  zeta_power : ∀ i, zeta i ^ n = 1
  zeta_injective : Function.Injective zeta

variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)
  (O : Constructions C)
  (H : ∀ (E : Type) [Field E], ℕ → Type v)
  [∀ (E : Type) [Field E] (n : ℕ), Group (H E n)]

/-- The SAME local representation and fixed coefficient equivalence. -/
def infinityObserver (E : Type) [Field E] :
    C (fiberScheme E) ⥤ FDRep ℂ (M.infinityGroup E) :=
  M.infinity E ⋙
    (FiniteRepresentationCoefficientTransport.coefficientEquivalence
      TwoAdicComplexEmbedding.complexEquiv (M.infinityGroup E)).functor

/-- The raw ordinary line object, with every rank and character guard retained. -/
def rawLine (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    C (affineLine K) :=
  (O.zero K h2).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))

/-- Base extension and open restriction are literal inverse images. -/
def localRaw (K E : Type) [Field K] [Fintype K] [Field E] [Algebra K E]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (n : ℕ) (hn : 0 < n) : C (fiberScheme E) :=
  (U.pull (localInputMorphism K E)).obj
    (rawLine (C := C) (O := O) K h2 ψ hψ n hn)

/-- Normalize by the actual line Tate object before that same pullback. -/
def localNormalizedThree (K E : Type) [Field K] [Fintype K] [Field E] [Algebra K E]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    C (fiberScheme E) :=
  (U.pull (localInputMorphism K E)).obj ((O.lineTate K h2 1).obj
    (rawLine (C := C) (O := O) K h2 ψ hψ 3 (by decide)))

/-- Precisely scoped GENERAL operation clauses on ONE compatible standard
theory. n<p is a stronger sufficient form of Fu's coprimality guard for
prime p. No clause concerns the correlation family or its Fourier bound. -/
structure GeneralFuInfinityClauses where
  powerCover : ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E]
    [CharP E p] (_h2E : (2 : E) ≠ 0) (n : ℕ) (_hn : 0 < n) (_hnp : n < p),
    PowerCoverData n E (M.infinityGroup E) (H E n)
  linearKernel : ∀ (K E : Type) [Field K] [Fintype K] [Field E]
    [IsAlgClosed E] [Algebra K E] (n : ℕ), C (affineLine K) → LinearASData E ℂ (H E n)
  quadraticPower : ∀ (E : Type) [Field E] [IsAlgClosed E]
    (_h2E : (2 : E) ≠ 0) (n : ℕ), ℕ → RepresentationFunctor ℂ (H E n) (H E n)
  quadraticEven : ∀ (E : Type) [Field E] [IsAlgClosed E]
    (h2E : (2 : E) ≠ 0) (n r : ℕ), Even r → ∀ A : FDRep ℂ (H E n),
    Representation.Equiv ((quadraticPower E h2E n r).obj A).ρ A.ρ
  tate : ∀ (K E : Type) [Field K] [Fintype K] [Field E]
    [IsAlgClosed E] [Algebra K E] (h2K : (2 : K) ≠ 0) (_h2E : (2 : E) ≠ 0)
    (z : ℤ) (A : C (affineLine K)),
    Representation.Equiv
      ((infinityObserver (C := C) (M := M) E).obj
        ((U.pull (localInputMorphism K E)).obj ((O.lineTate K h2K z).obj A))).ρ
      ((infinityObserver (C := C) (M := M) E).obj
        ((U.pull (localInputMorphism K E)).obj A)).ρ
  rawMonodromy : ∀ (p : ℕ) [Fact p.Prime] (K E : Type)
    [Field K] [Fintype K] [CharP K p] [Field E] [IsAlgClosed E]
    [Algebra K E] [CharP E p] (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (n : ℕ) (hn : 0 < n) (hnp : n < p),
    Representation.Equiv
      ((infinityObserver (C := C) (M := M) E).obj
        (localRaw (C := C) (U := U) (O := O) K E h2K ψ hψ n hn)).ρ
      ((powerCover p E h2E n hn hnp).push.obj
        ((quadraticPower E h2E n (n - 1)).obj
          ((linearKernel K E n (O.artinSchreier K h2K ψ)).phase (n : E)))).ρ

variable (R : GeneralFuInfinityClauses C U M O H)

/-- The n=3 power operations ARE the cubic operations, by construction. -/
def cubicCover (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E]
    [CharP E p] (h2E : (2 : E) ≠ 0) (hp : 3 < p) :
    CubicCoverData E ℂ (M.infinityGroup E) (H E 3) where
  push := (R.powerCover p E h2E 3 (by decide) hp).push
  pull := (R.powerCover p E h2E 3 (by decide) hp).pull
  deck := (R.powerCover p E h2E 3 (by decide) hp).deck
  zeta := (R.powerCover p E h2E 3 (by decide) hp).zeta
  zeta_cube := (R.powerCover p E h2E 3 (by decide) hp).zeta_power
  zeta_injective := (R.powerCover p E h2E 3 (by decide) hp).zeta_injective

/-- Apply the ALL-rank theorem at three, then eliminate Kummer exponent two. -/
def rawThreeModel (p : ℕ) [Fact p.Prime] (K E : Type)
    [Field K] [Fintype K] [CharP K p] [Field E] [IsAlgClosed E]
    [Algebra K E] [CharP E p] (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0)
    (hp : 3 < p) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    Representation.Equiv
      ((infinityObserver (C := C) (M := M) E).obj
        (localRaw (C := C) (U := U) (O := O) K E h2K ψ hψ 3 (by decide))).ρ
      ((cubicCover (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p E h2E hp).push.obj
        ((R.linearKernel K E 3 (O.artinSchreier K h2K ψ)).phase 3)).ρ :=
  (R.rawMonodromy p K E h2K h2E ψ hψ 3 (by decide) hp).trans
    ((R.powerCover p E h2E 3 (by decide) hp).push.mapEquiv
      (R.quadraticEven E h2E 3 2 (by decide) _))

/-- The actual normalized SAME-O primitive: geometric Tate only. -/
def normalizedThreeModel (p : ℕ) [Fact p.Prime] (K E : Type)
    [Field K] [Fintype K] [CharP K p] [Field E] [IsAlgClosed E]
    [Algebra K E] [CharP E p] (h2K : (2 : K) ≠ 0) (h2E : (2 : E) ≠ 0)
    (hp : 3 < p) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    Representation.Equiv
      ((infinityObserver (C := C) (M := M) E).obj
        (localNormalizedThree (C := C) (U := U) (O := O) K E h2K ψ hψ)).ρ
      ((cubicCover (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p E h2E hp).push.obj
        ((R.linearKernel K E 3 (O.artinSchreier K h2K ψ)).phase 3)).ρ :=
  (R.tate K E h2K h2E 1 (rawLine (C := C) (O := O) K h2K ψ hψ 3 (by decide))).trans
    (rawThreeModel (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p K E h2K h2E hp ψ hψ)

section ScalarApplication
variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K] [CharP K p]
  (h2K : (2 : K) ≠ 0) (h2E : (2 : PhaseField K) ≠ 0) (hp : 3 < p)
  (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1)
  {Q : Type w} [Category Q]
  (sourceOperations : SheafOperations (PhaseField K) (C (fiberScheme (PhaseField K))) Q)
  (scalarLaws : KloostermanInfinityFromScalar.ScalarRules sourceOperations
    (infinityObserver (C := C) (M := M) (PhaseField K))
    (cubicCover (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p (PhaseField K) h2E hp)
    (R.linearKernel K (PhaseField K) 3 (O.artinSchreier K h2K ψ)))

/-- Only the ALL-object scalar/base-change/linear substitution laws are
inputs; the normalized primitive model is the preceding theorem output. -/
def scalarInputs :
    KloostermanInfinityFromScalar.Inputs sourceOperations
      (infinityObserver (C := C) (M := M) (PhaseField K))
      (cubicCover (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p (PhaseField K) h2E hp)
      (R.linearKernel K (PhaseField K) 3 (O.artinSchreier K h2K ψ))
      (localNormalizedThree (C := C) (U := U) (O := O) K (PhaseField K) h2K ψ hψ) p where
  toScalarRules := scalarLaws
  sourceModel hp' := normalizedThreeModel (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p K (PhaseField K) h2K h2E hp' ψ hψ

/-- The former KR is constructed from GENERAL Fu and generic operation laws. -/
def computedInfinityRules :
    KloostermanInfinityRules p
      (cubicCover (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p (PhaseField K) h2E hp)
      (R.linearKernel K (PhaseField K) 3 (O.artinSchreier K h2K ψ))
      (sourceInfinity sourceOperations
        (infinityObserver (C := C) (M := M) (PhaseField K))
        (localNormalizedThree (C := C) (U := U) (O := O) K (PhaseField K) h2K ψ hψ)) :=
  (scalarInputs (C := C) (U := U) (M := M) (O := O) (H := H) (R := R) p K h2K h2E hp ψ hψ sourceOperations scalarLaws).kloostermanInfinityRules

end ScalarApplication
end PrimeGap182.TypeIII.GeneralFuPrimitiveInfinityApplication03

#print axioms PrimeGap182.TypeIII.GeneralFuPrimitiveInfinityApplication03.rawThreeModel
#print axioms PrimeGap182.TypeIII.GeneralFuPrimitiveInfinityApplication03.normalizedThreeModel
#print axioms PrimeGap182.TypeIII.GeneralFuPrimitiveInfinityApplication03.computedInfinityRules
