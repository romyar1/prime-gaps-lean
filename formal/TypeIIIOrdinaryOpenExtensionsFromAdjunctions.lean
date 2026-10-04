import TypeIIIQSTCompactBridgeFromCompactifiedDerivedPushforward
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Whiskering

/-!
# Ordinary open extensions characterized by SAME-U adjunctions

The interface is universal on quasi-compact open maps between separated
finite-type presentations over a field with two invertible. It supplies
ordinary bang and ordinary push only by their adjunctions with SAME U.pull,
exactness of bang and the genuine restriction unit. The ordinary support
map is computed as the right-adjunction mate of that inverse unit.

The universal derived interpretations retain exact single-bang agreement
and only H0 of derived open push on an ordinary single. No exact ordinary
push, concentration of derived push, or finished extension/support data is
assumed. Matching the supplied derived support map at H0 is a separate
ALL-open operation-interpretation capability.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PrimeGap182.TypeIII.OrdinaryOpenExtensionsFromAdjunctions
open ExactInverseImagesToDerived QSTCompactBridgeFromCompactifiedDerivedPushforward

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)

/-- ALL guarded actual open maps, not a chosen ambient extension system. -/
structure OrdinaryOpenFamily where
  bang : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j],
      j ≫ PY.structureMorphism = PX.structureMorphism → C X ⥤ C Y
  push : ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    ∀ {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j],
      j ≫ PY.structureMorphism = PX.structureMorphism → C X ⥤ C Y
  bangAdj : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
      (overField : j ≫ PY.structureMorphism = PX.structureMorphism),
      bang K h2 PX PY j overField ⊣ U.pull j
  pushAdj : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
      (overField : j ≫ PY.structureMorphism = PX.structureMorphism),
      U.pull j ⊣ push K h2 PX PY j overField
  bangExact : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
      (overField : j ≫ PY.structureMorphism = PX.structureMorphism),
      exactFunctor (C X) (C Y) (bang K h2 PX PY j overField)
  bangUnitIsIso : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
      (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
      (overField : j ≫ PY.structureMorphism = PX.structureMorphism),
      IsIso (bangAdj K h2 PX PY j overField).unit

variable (F : OrdinaryOpenFamily C U) (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
  {X Y : Scheme} (PX : FieldPresentation K X) (PY : FieldPresentation K Y)
  (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
  (overField : j ≫ PY.structureMorphism = PX.structureMorphism)

/-- The restriction comparison is the inverse of the actual left-adjunction unit. -/
def bangRestrictionIso : F.bang K h2 PX PY j overField ⋙ U.pull j ≅ 𝟭 (C X) := by
  letI := F.bangUnitIsIso K h2 PX PY j overField
  exact (asIso (F.bangAdj K h2 PX PY j overField).unit).symm

/-- The support map is derived from the two adjunctions and their genuine restriction unit. -/
def canonicalSupport : F.bang K h2 PX PY j overField ⟶ F.push K h2 PX PY j overField :=
  (Functor.rightUnitor (F.bang K h2 PX PY j overField)).inv ≫
    Functor.whiskerLeft (F.bang K h2 PX PY j overField)
      (F.pushAdj K h2 PX PY j overField).unit ≫
    (Functor.associator (F.bang K h2 PX PY j overField) (U.pull j)
      (F.push K h2 PX PY j overField)).inv ≫
    Functor.whiskerRight (bangRestrictionIso C U F K h2 PX PY j overField).hom
      (F.push K h2 PX PY j overField) ≫
    (Functor.leftUnitor (F.push K h2 PX PY j overField)).hom

theorem canonicalSupport_app (A : C X) :
    (canonicalSupport C U F K h2 PX PY j overField).app A =
      (F.pushAdj K h2 PX PY j overField).unit.app
        ((F.bang K h2 PX PY j overField).obj A) ≫
      (F.push K h2 PX PY j overField).map
        ((bangRestrictionIso C U F K h2 PX PY j overField).hom.app A) := by
  simp [canonicalSupport]

/-- Exact bang has intrinsic additivity; no extra coefficient dictionary is needed. -/
theorem bang_additive : (F.bang K h2 PX PY j overField).Additive :=
  exactFunctor_le_additiveFunctor (C X) (C Y) (F.bang K h2 PX PY j overField)
    (F.bangExact K h2 PX PY j overField)

/-- Ordinary direct image is left exact from its SAME-U right adjunction. -/
theorem push_preservesFiniteLimits : PreservesFiniteLimits (F.push K h2 PX PY j overField) := by
  let := (F.pushAdj K h2 PX PY j overField).rightAdjoint_preservesLimits
  infer_instance

/-- Only left exactness, not exact ordinary push, is obtained. -/
theorem push_additive : (F.push K h2 PX PY j overField).Additive :=
  leftExactFunctor_le_additiveFunctor (C X) (C Y) (F.push K h2 PX PY j overField)
    (push_preservesFiniteLimits C U F K h2 PX PY j overField)

local instance allSchemeLocalizations : ∀ Z : Scheme, HasDerivedCategory.{mu} (C Z) :=
  fun _ => HasDerivedCategory.standard _

/-- The ordinary single has its actual standard H0 comparison. -/
def degreeZeroH0Iso (Z : Scheme) :
    boundedDegreeZero C Z ⋙ cohomology C Z 0 ≅ 𝟭 (C Z) :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso (C Z) 0

/-- Two ALL-open derived interpretations, with no false Rpush-single concentration. -/
structure DerivedComparisons (M : Operations C) where
  singleBang : ∀ (B : Type) [Field B] (hB : (2 : B) ≠ 0)
    {S T : Scheme} (PS : FieldPresentation B S) (PT : FieldPresentation B T)
      (a : S ⟶ T) [IsOpenImmersion a] [QuasiCompact a]
      (overB : a ≫ PT.structureMorphism = PS.structureMorphism),
      ((F.bang B hB PS PT a overB ⋙ boundedDegreeZero C T) ≅
        (boundedDegreeZero C S ⋙ M.openBang B hB PS PT a overB))
  h0Push : ∀ (B : Type) [Field B] (hB : (2 : B) ≠ 0)
    {S T : Scheme} (PS : FieldPresentation B S) (PT : FieldPresentation B T)
      (a : S ⟶ T) [IsOpenImmersion a] [QuasiCompact a]
      (overB : a ≫ PT.structureMorphism = PS.structureMorphism),
      (((boundedDegreeZero C S ⋙ M.openPush B hB PS PT a overB) ⋙ cohomology C T 0) ≅
        F.push B hB PS PT a overB)

variable (M : Operations C) (D : DerivedComparisons C U F M)

/-- H0 of derived bang on an ordinary single is computed using the genuine single comparison. -/
def h0BangIso :
    (boundedDegreeZero C X ⋙ M.openBang K h2 PX PY j overField) ⋙ cohomology C Y 0 ≅
      F.bang K h2 PX PY j overField :=
  Functor.isoWhiskerRight (D.singleBang K h2 PX PY j overField).symm (cohomology C Y 0) ≪≫
    Functor.associator (F.bang K h2 PX PY j overField) (boundedDegreeZero C Y)
      (cohomology C Y 0) ≪≫
    Functor.isoWhiskerLeft (F.bang K h2 PX PY j overField) (degreeZeroH0Iso C Y) ≪≫
    Functor.rightUnitor (F.bang K h2 PX PY j overField)

/-- Matching H0 of the supplied derived support is precise universal operation interpretation. -/
def DerivedSupportCompatibility : Prop :=
  ∀ (B : Type) [Field B] (hB : (2 : B) ≠ 0)
    {S T : Scheme} (PS : FieldPresentation B S) (PT : FieldPresentation B T)
      (a : S ⟶ T) [IsOpenImmersion a] [QuasiCompact a]
      (overB : a ≫ PT.structureMorphism = PS.structureMorphism) (A : C S),
      (cohomology C T 0).map
          ((M.openSupport B hB PS PT a overB).app ((boundedDegreeZero C S).obj A)) ≫
        (D.h0Push B hB PS PT a overB).hom.app A =
      (h0BangIso C U F B hB PS PT a overB M D).hom.app A ≫
        (canonicalSupport C U F B hB PS PT a overB).app A

theorem derivedSupport_h0 (compatibility : DerivedSupportCompatibility C U F M D) (A : C X) :
    (cohomology C Y 0).map
        ((M.openSupport K h2 PX PY j overField).app ((boundedDegreeZero C X).obj A)) ≫
      (D.h0Push K h2 PX PY j overField).hom.app A =
    (h0BangIso C U F K h2 PX PY j overField M D).hom.app A ≫
      (canonicalSupport C U F K h2 PX PY j overField).app A :=
  compatibility K h2 PX PY j overField A

end PrimeGap182.TypeIII.OrdinaryOpenExtensionsFromAdjunctions
