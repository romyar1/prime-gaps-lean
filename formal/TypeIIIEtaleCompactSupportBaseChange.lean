import TypeIIIEtaleOpenExtensionBaseChange
import TypeIIIEtaleDerivedOpenBaseChange

/-!
# Base change with extension by zero on the pulled-back open

For a fixed open embedding j : U → X and a morphism q : X → S,
the existing derived base-change map on j_!F is followed by the
proved compatibility of j_! with inverse image.  Its target is thus
the actual higher direct image of extension by zero from the actual
pulled-back open, with all schemes given by literal pullbacks.

The construction retains the original derived map and its coefficient
sheaf.  The component formula records the original comparison followed
by higher direct image of the actual extension comparison.  It is an
isomorphism in the already established case of an open change of base.

The Kloosterman specialization uses the unchanged proper model and
original phase extension by zero.  No proper base-change theorem for
arbitrary base change, independence of compactification, or adic
cohomology comparison is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PrimeGap182.TypeIII.EtaleCompactSupportBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {U X S' S : Scheme.{u}} (q : X ⟶ S) (j : U ⟶ X)
  [Etale j] [Mono j] (g : S' ⟶ S) (E : Type u) [Ring E]

/-- The actual target: inverse image to the pulled-back open, extension
by zero into the pulled-back source, and its existing higher direct image. -/
def targetFunctor (n : ℕ) :
    Sheaf U.smallEtaleTopology (ModuleCat.{u} E) ⥤
      Sheaf S'.smallEtaleTopology (ModuleCat.{u} E) :=
  EtaleInverseImage.functor (pullback.snd (pullback.fst q g) j) E ⋙
    EtaleExtensionByZero.functor (pullback q g)
      (Scheme.Etale.mk (pullback.fst (pullback.fst q g) j)) E ⋙
      EtaleDerivedDirectImage.functor (pullback.snd q g) E n

/-- Higher direct image of the proved comparison with the actual
extension by zero on the pulled-back open. -/
def targetComparisonIso (n : ℕ) :
    EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E ⋙
        EtaleInverseImage.functor (pullback.fst q g) E ⋙
          EtaleDerivedDirectImage.functor (pullback.snd q g) E n ≅
      targetFunctor q j g E n :=
  Functor.isoWhiskerRight (EtaleOpenExtensionBaseChange.iso (pullback.fst q g) j E)
    (EtaleDerivedDirectImage.functor (pullback.snd q g) E n)

/-- The original derived comparison followed by the proved identification
of its target with higher direct image of the actual pulled-back extension. -/
def map (n : ℕ) :
    EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E ⋙
        EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor g E ⟶
      targetFunctor q j g E n :=
  Functor.whiskerLeft (EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E)
      (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n) ≫
    (targetComparisonIso q j g E n).hom

/-- The factorization uses the same previously constructed derived map. -/
theorem map_eq (n : ℕ) :
    map q j g E n =
      Functor.whiskerLeft (EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E)
          (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n) ≫
        (Functor.isoWhiskerRight
          (EtaleOpenExtensionBaseChange.iso (pullback.fst q g) j E)
          (EtaleDerivedDirectImage.functor (pullback.snd q g) E n)).hom := rfl

/-- On each original coefficient sheaf, first apply the original
derived comparison, then the higher direct image of the extension isomorphism. -/
theorem map_app (n : ℕ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} E)) :
    (map q j g E n).app F =
      (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n).app
          ((EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E).obj F) ≫
        (EtaleDerivedDirectImage.functor (pullback.snd q g) E n).map
          ((EtaleOpenExtensionBaseChange.iso (pullback.fst q g) j E).hom.app F) := rfl

variable [Etale g] [Mono g]

/-- The constructed map is invertible for the already proved open
case of derived base change. -/
instance map_isIso (n : ℕ) : IsIso (map q j g E n) := by
  let : IsIso (Functor.whiskerLeft
      (EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E)
      (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n)) :=
    (Functor.isoWhiskerLeft (EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E)
      (EtaleDerivedOpenBaseChange.pullbackBaseChangeIso q g E n)).isIso_hom
  unfold map
  infer_instance

/-- The open-base-change isomorphism with the actual pulled-back extension as target. -/
def openIso (n : ℕ) :
    EtaleExtensionByZero.functor X (Scheme.Etale.mk j) E ⋙
        EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor g E ≅
      targetFunctor q j g E n :=
  asIso (map q j g E n)

/-- Its forward map is exactly the constructed original-map/target-isomorphism composite. -/
theorem openIso_hom (n : ℕ) : (openIso q j g E n).hom = map q j g E n := rfl

end PrimeGap182.TypeIII.EtaleCompactSupportBaseChange

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) {T : Scheme.{0}}
  (g : T ⟶ Spec (.of (Polynomial (ZMod p)))) (E : Type) [Ring E]

/-- The comparison for the original compactified phase family, with
the actual pulled-back open extension in its target. -/
def kloostermanCompactSupportBaseChange (n : ℕ) :
    kloostermanCompactifiedDerivedImage p E n ⋙ EtaleInverseImage.functor g E ⟶
      EtaleCompactSupportBaseChange.targetFunctor (kloostermanCompactificationProjection p)
        (kloostermanCompactificationOpenImmersion p) g E n :=
  EtaleCompactSupportBaseChange.map (kloostermanCompactificationProjection p)
    (kloostermanCompactificationOpenImmersion p) g E n

/-- The fixed-family construction factors through the unchanged original
compactified derived comparison and the actual parameter-base extension isomorphism. -/
theorem kloostermanCompactSupportBaseChange_eq (n : ℕ) :
    kloostermanCompactSupportBaseChange p g E n =
      kloostermanCompactifiedDerivedBaseChange p g E n ≫
        (Functor.isoWhiskerRight
          (kloostermanPhaseExtensionByZero_parameterBaseChangeIso p E g)
          (EtaleDerivedDirectImage.functor
            (pullback.snd (kloostermanCompactificationProjection p) g) E n)).hom := rfl

/-- Its component retains the original phase coefficient sheaf and
the original derived comparison on its existing extension by zero. -/
theorem kloostermanCompactSupportBaseChange_app (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanCompactSupportBaseChange p g E n).app F =
      (kloostermanCompactifiedDerivedBaseChange p g E n).app F ≫
        (EtaleDerivedDirectImage.functor
          (pullback.snd (kloostermanCompactificationProjection p) g) E n).map
          ((kloostermanPhaseExtensionByZero_parameterBaseChangeIso p E g).hom.app F) := rfl

variable [Etale g] [Mono g]

/-- For an open change of the parameter base, the same fixed-family map is invertible. -/
instance kloostermanCompactSupportBaseChange_isIso (n : ℕ) :
    IsIso (kloostermanCompactSupportBaseChange p g E n) :=
  EtaleCompactSupportBaseChange.map_isIso (kloostermanCompactificationProjection p)
    (kloostermanCompactificationOpenImmersion p) g E n

/-- The corresponding open-base-change isomorphism for the unchanged phase family. -/
def kloostermanCompactSupportOpenBaseChangeIso (n : ℕ) :
    kloostermanCompactifiedDerivedImage p E n ⋙ EtaleInverseImage.functor g E ≅
      EtaleCompactSupportBaseChange.targetFunctor (kloostermanCompactificationProjection p)
        (kloostermanCompactificationOpenImmersion p) g E n :=
  asIso (kloostermanCompactSupportBaseChange p g E n)

/-- Its forward map is the same fixed-family comparison. -/
theorem kloostermanCompactSupportOpenBaseChangeIso_hom (n : ℕ) :
    (kloostermanCompactSupportOpenBaseChangeIso p g E n).hom =
      kloostermanCompactSupportBaseChange p g E n := rfl

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.targetFunctor
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.targetComparisonIso
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.map
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.map_eq
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.map_app
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.map_isIso
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.openIso
#print axioms PrimeGap182.TypeIII.EtaleCompactSupportBaseChange.openIso_hom
#print axioms PrimeGap182.TypeIII.kloostermanCompactSupportBaseChange
#print axioms PrimeGap182.TypeIII.kloostermanCompactSupportBaseChange_eq
#print axioms PrimeGap182.TypeIII.kloostermanCompactSupportBaseChange_app
#print axioms PrimeGap182.TypeIII.kloostermanCompactSupportBaseChange_isIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactSupportOpenBaseChangeIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactSupportOpenBaseChangeIso_hom
