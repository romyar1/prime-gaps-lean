import TypeIIIArithmeticSourcesFromOrigin
import TypeIIICanonicalCurveInput

/-!
# Arithmetic origin inputs from single geometric source models

The geometric models for every nonzero scalar are derived from the
unscaled source models and general tame scalar restriction. The latter
compares full geometric inertia, with lissity and tameness guards.
No comparison of full arithmetic Frobenius matrices is asserted.
The original invariant-stalk comparisons and raw Frobenius actions are
retained; the existing normalization proof gives the scalar q^-1.

Published interpretation: Katz GKM 7.4.3 and 4.3 for the single Kl3/AS
origin models; tame covering theory (Stacks 0EXW) for scalar restriction.
The same adic objects, local functors and coefficient embedding remain
general background inputs.
-/

noncomputable section
open CategoryTheory

namespace PrimeGap182.TypeIII.ArithmeticOriginFromScalar

open StartingSourceMaps ArithmeticSourceMaps ArithmeticSourceTransport
open ArithmeticPrimitiveSources ArithmeticSourcesFromOrigin
open CanonicalCurveInput RegularUnipotentRepresentation

universe u v w a b c d z
variable (K E : Type) [Field K] [Field E] [Algebra K E]
  {Line : Type u} [Category.{a} Line]
  {Input : Type v} [Category.{b} Input]
  {Local : Type w} [Category.{c} Local] {G : Type d} [Group G]
  {original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input}
  (P : Pullbacks (Local := Local) K E original) (J : Local ⥤ FDRep ℂ G)

/-- Full nearby geometric inertia of the literal unscaled source. -/
def primitiveInertia (A : Line) : FDRep ℂ G :=
  J.obj ((P.specialized (localInputMorphism K E)).obj A)

variable (LF : LocalFrobenius J) (LG : LineGeometry Line)
  [Fintype E] (twistOne : Line → Line) (raw as : Line)
  (tame : G →* Multiplicative ℂ)

/-- Single primitive models and general scalar restriction, together
with the original invariant-stalk arithmetic data. No family of Kl3 or
AS geometric scalar models is a field. -/
structure StalkData where
  origin : OriginStalks.{u,z} Line
  comparison : ScalarStalkComparison K E P J LF origin
  tate : TateOriginRules E origin twistOne
  scalarRestriction : ∀ (a : Eˣ) A, LG.LisseOnUnits A → LG.TameZero A →
    Representation.Equiv (J.obj (scalarSource K E P A a)).ρ
      (primitiveInertia K E P J A).ρ

/-- The primitive geometric models are added to the same arithmetic stalks. -/
structure Geometry extends StalkData K E P J LF LG twistOne where
  klModel : Representation.Equiv (primitiveInertia K E P J (twistOne raw)).ρ
    (tameRepresentation tame)
  asModel : Representation.Equiv (primitiveInertia K E P J as).ρ
    (Representation.trivial ℂ G ℂ)

/-- The original interface additionally records both arithmetic actions.
The live published application derives these from prime-field actions. -/
structure Inputs extends Geometry K E P J LF LG twistOne raw as tame where
  rawAction : ∀ v, origin.frobenius raw v = v
  asAction : ∀ v, origin.frobenius as v = v

variable {K E P J LF LG twistOne raw as tame}
  (S : Inputs K E P J LF LG twistOne raw as tame)

/-- Apply tame scalar restriction to the normalized Kloosterman source. -/
def Inputs.klZero (hkl : Kl3Properties LG (twistOne raw)) (a : Eˣ) :
    Representation.Equiv (J.obj (scalarSource K E P (twistOne raw) a)).ρ
      (tameRepresentation tame) :=
  (S.scalarRestriction a (twistOne raw) hkl.lisse hkl.tame).trans S.klModel

/-- Apply tame scalar restriction to the same AS source. -/
def Inputs.asZero (has : ASProperties LG as) (a : Eˣ) :
    Representation.Equiv (J.obj (scalarSource K E P as a)).ρ
      (Representation.trivial ℂ G ℂ) :=
  (S.scalarRestriction a as has.lisse has.tame).trans S.asModel

/-- Supply the old arithmetic origin interface from the derived models,
preserving its actual invariant stalks, comparisons and Frobenius actions. -/
def Inputs.toOriginInputs (hkl : Kl3Properties LG (twistOne raw))
    (has : ASProperties LG as) :
    ArithmeticSourcesFromOrigin.Inputs K E P J LF twistOne raw as tame where
  origin := S.origin
  comparison := S.comparison
  tate := S.tate
  klZero := S.klZero hkl
  asZero := S.asZero has
  rawAction := S.rawAction
  asAction := S.asAction

/-- The derived geometric models retain the checked arithmetic normalization. -/
theorem Inputs.primitiveSources_scalar (hkl : Kl3Properties LG (twistOne raw))
    (has : ASProperties LG as) :
    (S.toOriginInputs hkl has).primitiveSources.scalar = (Fintype.card E : ℂ)⁻¹ :=
  (S.toOriginInputs hkl has).primitiveSources_scalar

end PrimeGap182.TypeIII.ArithmeticOriginFromScalar

#print axioms PrimeGap182.TypeIII.ArithmeticOriginFromScalar.primitiveInertia
#print axioms PrimeGap182.TypeIII.ArithmeticOriginFromScalar.Inputs.klZero
#print axioms PrimeGap182.TypeIII.ArithmeticOriginFromScalar.Inputs.asZero
#print axioms PrimeGap182.TypeIII.ArithmeticOriginFromScalar.Inputs.toOriginInputs
#print axioms PrimeGap182.TypeIII.ArithmeticOriginFromScalar.Inputs.primitiveSources_scalar
