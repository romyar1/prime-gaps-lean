import TypeIIIArithmeticSourcePointFromLaurentSpecialization02

/-!
# Arithmetic Gm trace transport through individual operation realizations

The standard primitives are prescribed independently of C/U/F: continuous
constructible Qbar2 sheaves on Gm_E and Spec E, H^n a_! on ordinary inputs,
actual Laurent point pull, geometric stalk followed by a fixed scalar
embedding into C, and geometric Frobenius. Their interpretation/existence
remains an external MODEL cut, not a conclusion of this module.

The separately quantified published theorem is Laumon's rational-adic compact
trace formula on every valid standard package, every finite E with 2 nonzero,
and every ordinary constructible object. Native arithmetic-category compact
and point isomorphisms plus ONE all-V fiber/Frobenius square transport it.
Standard Frobenius naturality derives every operation square; the dictionary
contains no trace equality, native trace formula or completed TraceRules.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.StandardGmTraceFromFaithfulArithmeticOperations
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open ArithmeticSourcePointFromLaurentSpecialization

universe nu mu

/-- Independent standard primitives on ALL valid finite fields. The actual
continuous constructible interpretation is supplied separately, before p. -/
structure StandardGmPrimitives where
  Curve : ∀ (E : Type) [Field E] [Fintype E], (2 : E) ≠ 0 → Type
  Spec : ∀ (E : Type) [Field E] [Fintype E], (2 : E) ≠ 0 → Type
  [curveCategory : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Category.{nu} (Curve E h2)]
  [specCategory : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Category.{nu} (Spec E h2)]
  compact : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Fin 3 → Curve E h2 ⥤ Spec E h2
  pointPull : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Eˣ → Curve E h2 ⥤ Spec E h2
  fiber : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Spec E h2 ⥤ ModuleCat.{0} ℂ
  geometricFrobenius : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    fiber E h2 ⟶ fiber E h2
  finite : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0) (V : Spec E h2),
    FiniteDimensional ℂ ((fiber E h2).obj V)

attribute [instance] StandardGmPrimitives.curveCategory StandardGmPrimitives.specCategory

/-- Trace on the genuine geometric fiber after its prescribed scalar realization. -/
def standardTrace (S : StandardGmPrimitives.{nu}) (E : Type) [Field E] [Fintype E]
    (h2 : (2 : E) ≠ 0) (V : S.Spec E h2) : ℂ :=
  LinearMap.trace ℂ ((S.fiber E h2).obj V) ((S.geometricFrobenius E h2).app V).hom

/-- This predicate's argument contains NO native C/U/F/compact operations.
Its required semantics are the independently prescribed continuous constructible
Qbar2 categories, arithmetic H^n a_!, literal Laurent-point inverse images,
canonical geometric stalk, fixed-iota scalar realization and geometric Frobenius.
Its existence and semantic validity are external, never derived here. -/
structure PublishedStandardGmTrace
    (standardContinuousConstructibleInterpretation : StandardGmPrimitives.{nu} → Prop) : Prop where
  formula : ∀ (S : StandardGmPrimitives.{nu}), standardContinuousConstructibleInterpretation S →
    ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0) (A : S.Curve E h2),
    standardTrace S E h2 ((S.compact E h2 0).obj A) -
      standardTrace S E h2 ((S.compact E h2 1).obj A) +
      standardTrace S E h2 ((S.compact E h2 2).obj A) =
      ∑ z : Eˣ, standardTrace S E h2 ((S.pointPull E h2 z).obj A)

variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (AlgebraicGeometry.Spec (.of E)))

/-- Four individual GENERAL arithmetic operation cuts, all before a selected
prime: curve/spec realization, compact comparison, point comparison, and ONE
fiber realization with its all-V Frobenius square. No formula occurs here. -/
structure FaithfulArithmeticOperations (S : StandardGmPrimitives.{nu}) where
  curveRealization : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    C (ArithmeticSourceMaps.fiberScheme E) ⥤ S.Curve E h2
  specRealization : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    C (AlgebraicGeometry.Spec (.of E)) ⥤ S.Spec E h2
  compactIso : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0) (n : Fin 3),
    nativeCompact E h2 n ⋙ specRealization E h2 ≅
      curveRealization E h2 ⋙ S.compact E h2 n
  pointIso : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0) (z : Eˣ),
    U.pull (gmPoint E z) ⋙ specRealization E h2 ≅
      curveRealization E h2 ⋙ S.pointPull E h2 z
  fiberIso : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    F.fiber E ≅ specRealization E h2 ⋙ S.fiber E h2
  fiberFrobenius : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (V : C (AlgebraicGeometry.Spec (.of E))),
    (F.frobenius E).app V ≫ (fiberIso E h2).hom.app V =
      (fiberIso E h2).hom.app V ≫
        (S.geometricFrobenius E h2).app ((specRealization E h2).obj V)

variable {C U F nativeCompact}

/-- Trace conjugacy through an actual module isomorphism. -/
theorem trace_eq_of_frobenius_square {V W : ModuleCat.{0} ℂ} (e : V ≅ W)
    (a : V ⟶ V) (b : W ⟶ W) (square : a ≫ e.hom = e.hom ≫ b) :
    LinearMap.trace ℂ V a.hom = LinearMap.trace ℂ W b.hom := by
  have hn (v) : e.toLinearEquiv (a.hom v) = b.hom (e.toLinearEquiv v) :=
    congrArg (fun m => m.hom v) square
  have hc : e.toLinearEquiv.conj a.hom = b.hom := by
    ext v
    change e.toLinearEquiv (a.hom (e.toLinearEquiv.symm v)) = _
    rw [hn, e.toLinearEquiv.apply_symm_apply]
  exact (LinearMap.trace_conj' _ e.toLinearEquiv).symm.trans
    (congrArg (LinearMap.trace ℂ _) hc)

variable (S : StandardGmPrimitives.{nu})
  (D : FaithfulArithmeticOperations C U F nativeCompact S)
  (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)

/-- Compose the ONE fiber comparison with an arithmetic-category operation iso. -/
def operationFiberIso
    (H : C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (AlgebraicGeometry.Spec (.of E)))
    (K : S.Curve E h2 ⥤ S.Spec E h2)
    (operationIso : H ⋙ D.specRealization E h2 ≅ D.curveRealization E h2 ⋙ K) :
    H ⋙ F.fiber E ≅ (D.curveRealization E h2 ⋙ K) ⋙ S.fiber E h2 :=
  Functor.isoWhiskerLeft H (D.fiberIso E h2) ≪≫
    (Functor.associator H (D.specRealization E h2) (S.fiber E h2)).symm ≪≫
    Functor.isoWhiskerRight operationIso (S.fiber E h2)

/-- Standard naturality derives the operation square from ONE all-V square. -/
theorem operationFiberIso_frobenius
    (H : C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (AlgebraicGeometry.Spec (.of E)))
    (K : S.Curve E h2 ⥤ S.Spec E h2)
    (operationIso : H ⋙ D.specRealization E h2 ≅ D.curveRealization E h2 ⋙ K)
    (A : C (ArithmeticSourceMaps.fiberScheme E)) :
    (F.frobenius E).app (H.obj A) ≫
        (operationFiberIso S D E h2 H K operationIso).hom.app A =
      (operationFiberIso S D E h2 H K operationIso).hom.app A ≫
        (S.geometricFrobenius E h2).app
          (K.obj ((D.curveRealization E h2).obj A)) := by
  have hn : (S.geometricFrobenius E h2).app
        ((D.specRealization E h2).obj (H.obj A)) ≫
        (S.fiber E h2).map (operationIso.hom.app A) =
      (S.fiber E h2).map (operationIso.hom.app A) ≫
        (S.geometricFrobenius E h2).app
          (K.obj ((D.curveRealization E h2).obj A)) :=
    ((S.geometricFrobenius E h2).naturality (operationIso.hom.app A)).symm
  dsimp [operationFiberIso]
  simp only [Category.id_comp]
  rw [← Category.assoc, D.fiberFrobenius, Category.assoc, hn]
  exact (Category.assoc ..).symm

/-- The trace equality is derived, rather than part of the MODEL dictionary. -/
theorem operation_trace
    (H : C (ArithmeticSourceMaps.fiberScheme E) ⥤ C (AlgebraicGeometry.Spec (.of E)))
    (K : S.Curve E h2 ⥤ S.Spec E h2)
    (operationIso : H ⋙ D.specRealization E h2 ≅ D.curveRealization E h2 ⋙ K)
    (A : C (ArithmeticSourceMaps.fiberScheme E)) :
    LinearMap.trace ℂ ((F.fiber E).obj (H.obj A))
        ((F.frobenius E).app (H.obj A)).hom =
      standardTrace S E h2 (K.obj ((D.curveRealization E h2).obj A)) :=
  trace_eq_of_frobenius_square
    ((operationFiberIso S D E h2 H K operationIso).app A)
    ((F.frobenius E).app (H.obj A))
    ((S.geometricFrobenius E h2).app (K.obj ((D.curveRealization E h2).obj A)))
    (operationFiberIso_frobenius S D E h2 H K operationIso A)

include D in
/-- Laumon's separate ALL-standard/ALL-finite-field theorem transports to ALL
ordinary native objects using only the individual arithmetic operation cuts. -/
theorem nativeCompact_trace_formula
    (standardContinuousConstructibleInterpretation : StandardGmPrimitives.{nu} → Prop)
    (published : PublishedStandardGmTrace standardContinuousConstructibleInterpretation)
    (genuineStandard : standardContinuousConstructibleInterpretation S)
    (A : C (ArithmeticSourceMaps.fiberScheme E)) :
    LinearMap.trace ℂ ((F.fiber E).obj ((nativeCompact E h2 0).obj A))
        ((F.frobenius E).app ((nativeCompact E h2 0).obj A)).hom -
      LinearMap.trace ℂ ((F.fiber E).obj ((nativeCompact E h2 1).obj A))
        ((F.frobenius E).app ((nativeCompact E h2 1).obj A)).hom +
      LinearMap.trace ℂ ((F.fiber E).obj ((nativeCompact E h2 2).obj A))
        ((F.frobenius E).app ((nativeCompact E h2 2).obj A)).hom =
      ∑ z : Eˣ, LinearMap.trace ℂ ((F.fiber E).obj ((U.pull (gmPoint E z)).obj A))
        ((F.frobenius E).app ((U.pull (gmPoint E z)).obj A)).hom := by
  rw [operation_trace S D E h2 (nativeCompact E h2 0) (S.compact E h2 0)
      (D.compactIso E h2 0) A,
    operation_trace S D E h2 (nativeCompact E h2 1) (S.compact E h2 1)
      (D.compactIso E h2 1) A,
    operation_trace S D E h2 (nativeCompact E h2 2) (S.compact E h2 2)
      (D.compactIso E h2 2) A]
  rw [published.formula S genuineStandard]
  apply Finset.sum_congr rfl
  intro z _
  exact (operation_trace S D E h2 (U.pull (gmPoint E z)) (S.pointPull E h2 z)
    (D.pointIso E h2 z) A).symm

end PrimeGap182.TypeIII.StandardGmTraceFromFaithfulArithmeticOperations
