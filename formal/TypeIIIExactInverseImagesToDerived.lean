import TypeIIISourceInverseImageSystem
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Canonical derived lift of one general exact inverse-image system

The ordinary categories are indexed by ACTUAL schemes. Their exact
inverse-image functors and ordinary identity/composition isomorphisms
are general framework data. A chosen derived localization may be used;
the standard localization is also constructed at the standard universe.
The derived categories, inverse images, degree-zero embeddings, derived
composition, shift compatibility and ordinary H^-2(K[1])=H^-1(K) are
constructed from Mathlib's actual functors and localization API.
No law assuming any of those derived conclusions is an input.

The sum-index extension below includes every original B index, scheme
and ordinary object type literally. In particular its source-line index
is the original B.Obj.line over the original coefficient field. Newly
needed schemes and their ordinary categories remain an explicit extension
realization. Wild inertia, fundamental-group transport, perverse curve
realization, coefficient limits and original PhaseData recognition are
outside this bounded construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.ExactInverseImagesToDerived

universe v w d ii
variable {I : Type ii} (X : I → Scheme) (C : I → Type v)
  [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]

/-- Only ORDINARY exact inverse-image data on actual indexed schemes. -/
structure OrdinarySystem where
  pull : ∀ {i j}, (X i ⟶ X j) → C j ⥤ C i
  identity : ∀ i, pull (𝟙 (X i)) ≅ 𝟭 (C i)
  composition : ∀ {i j k} (f : X i ⟶ X j) (g : X j ⟶ X k),
    pull g ⋙ pull f ≅ pull (f ≫ g)
  [additive : ∀ {i j} (f : X i ⟶ X j), (pull f).Additive]
  [limits : ∀ {i j} (f : X i ⟶ X j), PreservesFiniteLimits (pull f)]
  [colimits : ∀ {i j} (f : X i ⟶ X j), PreservesFiniteColimits (pull f)]

attribute [instance] OrdinarySystem.additive OrdinarySystem.limits OrdinarySystem.colimits

@[instance_reducible]
def OrdinarySystem.standardLocalizations (_A : OrdinarySystem X C) :
    ∀ i, HasDerivedCategory.{max v w} (C i) := fun i => HasDerivedCategory.standard (C i)

/-- An ORDINARY natural isomorphism between exact functors induces the
canonical derived natural isomorphism, by localization. -/
def derivedNatIso {C1 C2 : Type v} [Category.{w} C1] [Category.{w} C2]
    [Abelian C1] [Abelian C2] [HasDerivedCategory.{d} C1] [HasDerivedCategory.{d} C2]
    {F G : C1 ⥤ C2} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory := by
  let Q1 := DerivedCategory.Q (C := C1)
  let Q2 := DerivedCategory.Q (C := C2)
  let Hf := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q2
  let Hg := G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q2
  letI : Localization.Lifting Q1 (HomologicalComplex.quasiIso C1 (ComplexShape.up ℤ))
      Hf F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors⟩
  letI : Localization.Lifting Q1 (HomologicalComplex.quasiIso C1 (ComplexShape.up ℤ))
      Hg G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors⟩
  exact Localization.liftNatIso Q1 (HomologicalComplex.quasiIso C1 (ComplexShape.up ℤ))
    Hf Hg F.mapDerivedCategory G.mapDerivedCategory
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) Q2)

variable {X C} (A : OrdinarySystem X C)
  [∀ i, HasDerivedCategory.{d} (C i)]

abbrev OrdinarySystem.Derived (_A : OrdinarySystem X C) (i : I) := DerivedCategory (C i)

def OrdinarySystem.derivedPull {i j} (f : X i ⟶ X j) :
    A.Derived j ⥤ A.Derived i := (A.pull f).mapDerivedCategory

def OrdinarySystem.degreeZero (i : I) : C i ⥤ A.Derived i :=
  DerivedCategory.singleFunctor (C i) 0

def OrdinarySystem.shiftOne (i : I) : A.Derived i ⥤ A.Derived i :=
  shiftFunctor (A.Derived i) (1 : ℤ)

/-- Ordinary cohomology of cochain complexes, not perverse cohomology. -/
def OrdinarySystem.ordinary (i : I) (n : ℤ) : A.Derived i ⥤ C i :=
  DerivedCategory.homologyFunctor (C i) n

def OrdinarySystem.degreeZeroPullback {i j} (f : X i ⟶ X j) :
    A.degreeZero j ⋙ A.derivedPull f ≅ A.pull f ⋙ A.degreeZero i :=
  (A.pull f).mapDerivedCategorySingleFunctor 0

def OrdinarySystem.pullShift {i j} (f : X i ⟶ X j) :
    A.shiftOne j ⋙ A.derivedPull f ≅ A.derivedPull f ⋙ A.shiftOne i :=
  (A.pull f).mapDerivedCategory.commShiftIso (1 : ℤ)

/-- The actual ordinary H^-2(K[1])=H^-1(K) natural isomorphism. -/
def OrdinarySystem.ordinaryShift (i : I) :
    A.shiftOne i ⋙ A.ordinary i (-2) ≅ A.ordinary i (-1) :=
  (DerivedCategory.homologyFunctor (C i) 0).shiftIso (1 : ℤ) (-2) (-1) (by decide)

/-- Derived composition is induced by ordinary composition on cochain
complexes, then uniquely lifted through the derived localization. -/
def OrdinarySystem.derivedComposition {i j k} (f : X i ⟶ X j) (g : X j ⟶ X k) :
    A.derivedPull g ⋙ A.derivedPull f ≅ A.derivedPull (f ≫ g) := by
  let Qk := DerivedCategory.Q (C := C k)
  let Qi := DerivedCategory.Q (C := C i)
  let H := (A.pull (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Qi
  have e : Qk ⋙ (A.derivedPull g ⋙ A.derivedPull f) ≅ H :=
    (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight (A.pull g).mapDerivedCategoryFactors _ ≪≫
      Functor.associator .. ≪≫
      Functor.isoWhiskerLeft _ (A.pull f).mapDerivedCategoryFactors ≪≫
      (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (A.composition f g) (ComplexShape.up ℤ)) Qi
  letI : Localization.Lifting Qk
      (HomologicalComplex.quasiIso (C k) (ComplexShape.up ℤ)) H
      (A.derivedPull g ⋙ A.derivedPull f) := ⟨e⟩
  letI : Localization.Lifting Qk
      (HomologicalComplex.quasiIso (C k) (ComplexShape.up ℤ)) H
      (A.derivedPull (f ≫ g)) := ⟨(A.pull (f ≫ g)).mapDerivedCategoryFactors⟩
  exact Localization.liftNatIso Qk
    (HomologicalComplex.quasiIso (C k) (ComplexShape.up ℤ)) H H
    (A.derivedPull g ⋙ A.derivedPull f) (A.derivedPull (f ≫ g)) (Iso.refl H)

def OrdinarySystem.derivedIdentity (i : I) :
    A.derivedPull (𝟙 (X i)) ≅ 𝟭 (A.Derived i) := by
  let Q := DerivedCategory.Q (C := C i)
  let H := (A.pull (𝟙 (X i))).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q
  have e : H ≅ Q :=
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (A.identity i) (ComplexShape.up ℤ)) Q ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso (C i) (ComplexShape.up ℤ)) Q ≪≫
      Functor.leftUnitor Q
  letI : Localization.Lifting Q
      (HomologicalComplex.quasiIso (C i) (ComplexShape.up ℤ)) Q (𝟭 (A.Derived i)) :=
    ⟨Functor.rightUnitor Q⟩
  letI : Localization.Lifting Q
      (HomologicalComplex.quasiIso (C i) (ComplexShape.up ℤ)) H
      (A.derivedPull (𝟙 (X i))) := ⟨(A.pull (𝟙 (X i))).mapDerivedCategoryFactors⟩
  exact Localization.liftNatIso Q
    (HomologicalComplex.quasiIso (C i) (ComplexShape.up ℤ)) H Q
    (A.derivedPull (𝟙 (X i))) (𝟭 (A.Derived i)) e

section OriginalExtension

open SourceInverseImageSystem
variable {K : Type} [Field K] (B : System.{v,w} K)
  {J : Type} (extraScheme : J → Scheme) (extraObj : J → Type v)

def originalSystem : OrdinarySystem (scheme K) B.Obj where
  pull f := B.pull f
  identity i := B.identity i
  composition f g := B.composition f g

/-- The original indices are included by Sum.inl, with no replacement
source-line scheme or independent coefficient-line choice. -/
def extensionScheme : Space K ⊕ J → Scheme :=
  Sum.elim (scheme K) extraScheme

def extensionObjects : Space K ⊕ J → Type v := Sum.elim B.Obj extraObj

instance extensionCategory [∀ j, Category.{w} (extraObj j)] :
    ∀ i, Category.{w} (extensionObjects B extraObj i) := by
  intro i
  cases i with
  | inl old => exact B.category old
  | inr new => change Category.{w} (extraObj new); infer_instance

instance extensionAbelian [∀ j, Category.{w} (extraObj j)] [∀ j, Abelian (extraObj j)] :
    ∀ i, Abelian (extensionObjects B extraObj i) := by
  intro i
  cases i with
  | inl old => exact B.abelian old
  | inr new => change Abelian (extraObj new); infer_instance

instance extensionLocalizations [∀ j, Category.{w} (extraObj j)] [∀ j, Abelian (extraObj j)]
    [old : ∀ i, HasDerivedCategory.{d} (B.Obj i)]
    [new : ∀ j, HasDerivedCategory.{d} (extraObj j)] :
    ∀ i, HasDerivedCategory.{d} (extensionObjects B extraObj i) := by
  intro i
  cases i with
  | inl i => exact old i
  | inr j => exact new j

theorem sourceLineScheme :
    extensionScheme extraScheme (Sum.inl (.line : Space K)) = StartingSourceMaps.affineLine K := rfl

theorem sourceLineObjects :
    extensionObjects B extraObj (Sum.inl (.line : Space K)) = B.Obj .line := rfl

/-- Ordinary agreement of the extended system with the original B.
This is part of the missing ORDINARY extension realization, not a law
assuming any derived degree/shift/composition conclusion. -/
structure OriginalPullAgreement [∀ j, Category.{w} (extraObj j)] [∀ j, Abelian (extraObj j)]
    (A : OrdinarySystem (extensionScheme extraScheme) (extensionObjects B extraObj)) : Prop where
  pull : ∀ {i j : Space K} (f : scheme K i ⟶ scheme K j),
    A.pull (i := Sum.inl i) (j := Sum.inl j) f = B.pull f

variable [∀ j, Category.{w} (extraObj j)] [∀ j, Abelian (extraObj j)]
  [∀ i, HasDerivedCategory.{d} (B.Obj i)] [∀ j, HasDerivedCategory.{d} (extraObj j)]
  (A : OrdinarySystem (extensionScheme extraScheme) (extensionObjects B extraObj))

/-- The extended source-line degree-zero embedding is literally the
original B source-line embedding, with the same chosen localization. -/
theorem sourceLineDegreeZero :
    A.degreeZero (Sum.inl (.line : Space K)) = (originalSystem B).degreeZero .line := rfl

def OriginalPullAgreement.derivedPull (R : OriginalPullAgreement B extraScheme extraObj A)
    {i j : Space K} (f : scheme K i ⟶ scheme K j) :
    A.derivedPull (i := Sum.inl i) (j := Sum.inl j) f ≅ (originalSystem B).derivedPull f := by
  exact derivedNatIso (eqToIso (R.pull f))

end OriginalExtension

end PrimeGap182.TypeIII.ExactInverseImagesToDerived

#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.OrdinarySystem.degreeZeroPullback
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.OrdinarySystem.pullShift
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.OrdinarySystem.ordinaryShift
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.OrdinarySystem.derivedComposition
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.OrdinarySystem.derivedIdentity
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.sourceLineScheme
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.sourceLineObjects
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.sourceLineDegreeZero
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.OriginalPullAgreement.derivedPull
#print axioms PrimeGap182.TypeIII.ExactInverseImagesToDerived.derivedNatIso
