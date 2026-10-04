import TypeIIIQSTGenericFiberFromActualGenericPoint

/-!
# Generic rank of the SAME Katz class from general published rank theorems

The published raw Katz rank theorem is required for EVERY valid disjoint
positive-rank index over EVERY finite field, not only the selected Kl3.
General ordinary Tate-rank invariance is required for ALL ordinary Gm objects and
integer twists. These statements use the SAME actual generic point, U and G.
The constructed class's entire hypergeometric_rank clause follows by the
actual Tate recipe, degree-zero construction and isomorphism transport.
Balanced families are measured at the generic point, without a global
lissity premise or evaluation at their possible singular point one.

Primary raw-rank source: Katz, Exponential Sums and Differential Equations,
Theorem8.4.2(6)--(8): https://web.math.princeton.edu/~nmk/wholebookcorrms.pdf.
The two general theorem parameters remain explicit; their true continuous
adic interpretation is not supplied by these conditional Lean applications.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.QSTHypergeometricRankFromGeneralKatzRank
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward
open QSTPrimitiveBridgesFromCommonKatzConstruction QSTGenericFiberFromActualGenericPoint

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (O : Constructions C)

local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable
  (ordinaryKatzRank : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K),
    Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((boundedDegreeZero C _).obj (O.katz K h2 { a with tateTwist := 0 }))) = a.rank)
  (ordinaryTateRank : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (n : ℤ) (A : C (ArithmeticSourceMaps.fiberScheme K)),
    Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((boundedDegreeZero C _).obj ((O.tate K h2 n).obj A))) =
    Module.finrank ℂ ((rawGenericFiber K C U G).obj ((boundedDegreeZero C _).obj A)))

include ordinaryKatzRank ordinaryTateRank in
/-- ALL genuine members have their actual index rank, including all Tate twists. -/
theorem member_genericRank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K) :
    Module.finrank ℂ (genericFiber K C U G ((boundedDegreeZero C _).obj (member C O K h2 a))) = a.rank := by
  rw [genericFiber_finrank]
  change Module.finrank ℂ ((rawGenericFiber K C U G).obj
    ((boundedDegreeZero C _).obj ((O.tate K h2 a.tateTwist).obj
      (O.katz K h2 { a with tateTwist := 0 })))) = a.rank
  rw [ordinaryTateRank]
  exact ordinaryKatzRank K h2 a

include ordinaryKatzRank ordinaryTateRank in
/-- The whole isomorphism-closed hypergeometric class has its actual generic rank. -/
theorem hypergeometric_genericRank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (A : Bounded C (ArithmeticSourceMaps.fiberScheme K)) (r : ℕ)
    (hA : hypergeometric C O K h2 A r) :
    Module.finrank ℂ (genericFiber K C U G A) = r := by
  obtain ⟨a, hr, ⟨e⟩⟩ := hA
  rw [genericFiber_finrank_iso K C U G e, member_genericRank C U G O ordinaryKatzRank ordinaryTateRank K h2 a]
  exact hr

section CanonicalQST
variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)

include ordinaryKatzRank ordinaryTateRank in
/-- Exact original ALL-member clause when Background uses the SAME computed fiber. -/
theorem qst_hypergeometric_rank
    (A : QSTRealizationFromExactInverseImages.Obj (CanonicalPrimeFramework.primeSource C U p)
      (QSTPerverseBackgroundFromUniversalHeart.domain C U p) .gm) (r : ℕ)
    (hA : qstHypergeometric C O U p h2 A r) :
    Module.finrank ℂ (genericFiber (ZMod p) C U G A) = r :=
  hypergeometric_genericRank C U G O ordinaryKatzRank ordinaryTateRank (ZMod p) h2 A r hA
end CanonicalQST

end PrimeGap182.TypeIII.QSTHypergeometricRankFromGeneralKatzRank
