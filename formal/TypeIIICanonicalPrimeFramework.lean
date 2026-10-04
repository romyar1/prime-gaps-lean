import TypeIIIUniversalOrdinaryInverseImages
import TypeIIIQSTRealizationFromExactInverseImages

/-!
# Canonical prime-indexed restrictions of one ordinary framework

C and U are fixed before the prime. The original source, native origin,
trait and actual auxiliary scheme categories are literal restrictions of
C; all ordinary pulls come from U. No Inputs or alternate source-system
agreement is supplied. The arithmetic QST plane and geometric native
plane remain different actual schemes.

This constructs the ordinary framework assignments and their standard
derived degree-zero comparisons. Adic interpretation, bounded/perverse
admissibility, derived tensor/compact/Tate operations, original character
and stalk/coefficient realizations remain explicit general framework data.
It does not construct a complete compatible residual Inputs family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.CanonicalPrimeFramework
open ExactInverseImagesToDerived

universe mu
variable (C : Scheme → Type)
  [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

variable (p : ℕ) [Fact p.Prime]

abbrev primeSource : SourceInverseImageSystem.System.{0,mu} (ZMod p) :=
  UniversalOrdinaryInverseImages.sourceSystem C U (ZMod p)

abbrev nativeOrdinary (i : OriginRealizationFromExactInverseImages.Index) : Type :=
  UniversalOrdinaryInverseImages.nativeOrdinary C (AlgebraicClosure (ZMod p)) i

abbrev localOrdinary : Type :=
  UniversalOrdinaryInverseImages.localOrdinary C (AlgebraicClosure (ZMod p))

abbrev auxiliaryOrdinary (i : NativeAuxiliarySchemes.Space) : Type :=
  UniversalOrdinaryInverseImages.auxiliaryOrdinary C (ZMod p) (AlgebraicClosure (ZMod p)) i

abbrev extraScheme :=
  UniversalOrdinaryInverseImages.extraScheme (ZMod p) (AlgebraicClosure (ZMod p))

abbrev extraOrdinary :=
  UniversalOrdinaryInverseImages.extraOrdinary C (ZMod p) (AlgebraicClosure (ZMod p))

local instance nativeCategory : ∀ i, Category.{mu} (nativeOrdinary C p i) :=
  fun _ => inferInstance
local instance nativeAbelian : ∀ i, Abelian (nativeOrdinary C p i) :=
  fun _ => inferInstance
local instance auxiliaryCategory : ∀ i, Category.{mu} (auxiliaryOrdinary C p i) :=
  fun _ => inferInstance
local instance auxiliaryAbelian : ∀ i, Abelian (auxiliaryOrdinary C p i) :=
  fun _ => inferInstance

abbrev primeCommon : OrdinarySystem (extensionScheme (extraScheme p))
    (extensionObjects (primeSource C U p) (extraOrdinary C p)) :=
  UniversalOrdinaryInverseImages.ordinaryA C U (ZMod p) (AlgebraicClosure (ZMod p))

theorem originalAgreement : OriginalPullAgreement (primeSource C U p)
    (extraScheme p) (extraOrdinary C p) (primeCommon C U p) :=
  UniversalOrdinaryInverseImages.originalAgreement C U (ZMod p) (AlgebraicClosure (ZMod p))

/-- The native curve, plane and origin use the same restricted U. -/
def primeNative : OrdinarySystem
    (OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)))
    (nativeOrdinary C p) :=
  OriginPoleFromExactInverseImages.nativeSystem (primeCommon C U p)

abbrev qstPlaneIndex : OriginPoleFromExactInverseImages.Extra NativeAuxiliarySchemes.Space :=
  Sum.inr (Sum.inr NativeAuxiliarySchemes.Space.arithmeticPlane)

abbrev qstOrdinary (i : UniformComplexityFromCommonRealization.Space) : Type :=
  QSTRealizationFromExactInverseImages.qstObjects (primeSource C U p)
    (extraOrdinary C p) qstPlaneIndex i

/-- QST is the existing actual-index constructor applied to the same A. -/
def primeQST : OrdinarySystem (UniformComplexityFromCommonRealization.scheme (ZMod p))
    (qstOrdinary C U p) :=
  QSTRealizationFromExactInverseImages.qstSystem (primeSource C U p)
    (extraScheme p) (extraOrdinary C p) qstPlaneIndex rfl (primeCommon C U p)

theorem qstObjects (i : UniformComplexityFromCommonRealization.Space) :
    qstOrdinary C U p i = C (UniformComplexityFromCommonRealization.scheme (ZMod p) i) := by
  cases i <;> rfl

/-- Every original map uses U, with the intrinsic category instances. -/
theorem sourcePullUsesU {i j : SourceInverseImageSystem.Space (ZMod p)}
    (f : SourceInverseImageSystem.scheme (ZMod p) i ⟶
      SourceInverseImageSystem.scheme (ZMod p) j) :
    (primeSource C U p).pull f = U.pull f := rfl

theorem nativePullUsesU {i j : OriginRealizationFromExactInverseImages.Index}
    (f : OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) i ⟶
      OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) j) :
    (primeNative C U p).pull f = U.pull f := rfl

/-- HEq only accommodates the finite-index expression of the literal
object categories. After exposing either index, the pull is U itself. -/
theorem qstPullUsesU {i j : UniformComplexityFromCommonRealization.Space}
    (f : UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶
      UniformComplexityFromCommonRealization.scheme (ZMod p) j) :
    HEq ((primeQST C U p).pull f) (U.pull f) := by
  cases i <;> cases j <;> rfl

local instance nativeLocalizations : ∀ i,
    HasDerivedCategory.{mu} (nativeOrdinary C p i) :=
  fun _ => HasDerivedCategory.standard _
local instance qstLocalizations : ∀ i,
    HasDerivedCategory.{mu} (qstOrdinary C U p i) :=
  fun _ => HasDerivedCategory.standard _
local instance allSchemeLocalizations : ∀ X : Scheme,
    HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

theorem nativeDegreeZeroUsesU (i : OriginRealizationFromExactInverseImages.Index) :
    (primeNative C U p).degreeZero i = U.degreeZero
      (OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) i) := rfl

theorem qstDegreeZeroUsesU (i : UniformComplexityFromCommonRealization.Space) :
    HEq ((primeQST C U p).degreeZero i)
      (U.degreeZero (UniformComplexityFromCommonRealization.scheme (ZMod p) i)) := by
  cases i <;> rfl

/-- Every actual native map has its constructed degree-zero comparison. -/
def nativeDegreeZeroPullback {i j : OriginRealizationFromExactInverseImages.Index}
    (f : OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) i ⟶
      OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) j) :
    (primeNative C U p).degreeZero j ⋙ (primeNative C U p).derivedPull f ≅
      (primeNative C U p).pull f ⋙ (primeNative C U p).degreeZero i :=
  (primeNative C U p).degreeZeroPullback f

/-- QST's ordinary objects and every derived pullback use the same A. -/
def qstDegreeZeroPullback {i j : UniformComplexityFromCommonRealization.Space}
    (f : UniformComplexityFromCommonRealization.scheme (ZMod p) i ⟶
      UniformComplexityFromCommonRealization.scheme (ZMod p) j) :
    (primeQST C U p).degreeZero j ⋙ (primeQST C U p).derivedPull f ≅
      (primeQST C U p).pull f ⋙ (primeQST C U p).degreeZero i :=
  (primeQST C U p).degreeZeroPullback f

/-- The whole prime-indexed ordinary agreement is available with C/U
already fixed. A p-free parameter type alone would not ensure this. -/
theorem originalAgreementFamily : ∀ p : ℕ, ∀ (_ : Fact p.Prime),
    OriginalPullAgreement (primeSource C U p) (extraScheme p)
      (extraOrdinary C p) (primeCommon C U p) :=
  fun p _ => originalAgreement C U p

end PrimeGap182.TypeIII.CanonicalPrimeFramework

#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.originalAgreement
#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.qstPullUsesU
#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.nativeDegreeZeroUsesU
#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.qstDegreeZeroUsesU
#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.nativeDegreeZeroPullback
#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.qstDegreeZeroPullback
#print axioms PrimeGap182.TypeIII.CanonicalPrimeFramework.originalAgreementFamily
