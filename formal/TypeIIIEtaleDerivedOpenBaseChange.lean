import TypeIIIDerivedBaseChangeIso
import TypeIIIEtaleDerivedBaseChange
import TypeIIIEtaleOpenBaseChange

/-!
# Derived open base change for the actual small étale functors

For an étale monomorphism `g`, the existing canonical derived pullback
map is invertible in every nonnegative degree, for arbitrary `q` and
any coefficient ring.  The ordinary comparison is the proved original
open base-change mate.  Its pulled-back inverse image preserves
injectives because the actual pullback projection is again an étale
monomorphism.  Thus the generic criterion applies to the same previously
constructed derived map.

The final specialization uses the unchanged Kloosterman compactification
and its existing extension by zero.  No proper-base-change or arbitrary
geometric-point base-change theorem is asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleDerivedOpenBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X S' S : Scheme.{u}} (q : X ⟶ S) (g : S' ⟶ S)
  [Etale g] [Mono g] (E : Type u) [Ring E]

set_option backward.isDefEq.respectTransparency false in
/-- The same canonical derived pullback map is invertible for an étale monomorphism. -/
instance pullbackBaseChangeMap_isIso (n : ℕ) :
    IsIso (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n) := by
  let : (EtaleInverseImage.functor (pullback.fst q g) E).PreservesInjectiveObjects :=
    EtaleRestrictionInverseImage.inverseImage_preservesInjectiveObjects_of_etale_mono
      (pullback.fst q g) E
  let : IsIso (EtaleInverseImage.pullbackBaseChangeMap q g E) :=
    EtaleOpenBaseChange.pullbackBaseChangeMap_isIso q g E
  rw [EtaleDerivedBaseChange.pullbackBaseChangeMap_eq]
  exact derivedBaseChangeMap_isIso (EtaleDirectImage.functor q E)
    (EtaleDirectImage.functor (pullback.snd q g) E)
    (EtaleInverseImage.functor (pullback.fst q g) E) (EtaleInverseImage.functor g E)
    (EtaleInverseImage.pullbackBaseChangeMap q g E) n

/-- The actual derived open base-change isomorphism in degree `n`. -/
def pullbackBaseChangeIso (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙ EtaleInverseImage.functor g E ≅
      EtaleInverseImage.functor (pullback.fst q g) E ⋙
        EtaleDerivedDirectImage.functor (pullback.snd q g) E n :=
  asIso (EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n)

/-- Its forward natural transformation is precisely the existing derived map. -/
theorem pullbackBaseChangeIso_hom (n : ℕ) :
    (pullbackBaseChangeIso q g E n).hom =
      EtaleDerivedBaseChange.pullbackBaseChangeMap q g E n := rfl

end PrimeGap182.TypeIII.EtaleDerivedOpenBaseChange

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) {T : Scheme.{0}}
  (g : T ⟶ Spec (.of (Polynomial (ZMod p)))) [Etale g] [Mono g]
  (E : Type) [Ring E]

set_option backward.isDefEq.respectTransparency false in
/-- The existing compactified Kloosterman base-change map is invertible
when the change of base is an étale monomorphism. -/
instance kloostermanCompactifiedDerivedBaseChange_isIso (n : ℕ) :
    IsIso (kloostermanCompactifiedDerivedBaseChange p g E n) :=
  (Functor.isoWhiskerLeft (kloostermanPhaseExtensionByZero p E)
    (EtaleDerivedOpenBaseChange.pullbackBaseChangeIso
      (kloostermanCompactificationProjection p) g E n)).isIso_hom

/-- Derived open base change for the unchanged compactification and existing extension by zero. -/
def kloostermanCompactifiedDerivedOpenBaseChangeIso (n : ℕ) :
    kloostermanCompactifiedDerivedImage p E n ⋙ EtaleInverseImage.functor g E ≅
      kloostermanPhaseExtensionByZero p E ⋙
        EtaleInverseImage.functor (pullback.fst (kloostermanCompactificationProjection p) g) E ⋙
          EtaleDerivedDirectImage.functor
            (pullback.snd (kloostermanCompactificationProjection p) g) E n :=
  asIso (kloostermanCompactifiedDerivedBaseChange p g E n)

/-- The fixed-model isomorphism retains exactly the original derived comparison. -/
theorem kloostermanCompactifiedDerivedOpenBaseChangeIso_hom (n : ℕ) :
    (kloostermanCompactifiedDerivedOpenBaseChangeIso p g E n).hom =
      kloostermanCompactifiedDerivedBaseChange p g E n := rfl

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.EtaleDerivedOpenBaseChange.pullbackBaseChangeMap_isIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedOpenBaseChange.pullbackBaseChangeIso
#print axioms PrimeGap182.TypeIII.EtaleDerivedOpenBaseChange.pullbackBaseChangeIso_hom
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedBaseChange_isIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedOpenBaseChangeIso
#print axioms PrimeGap182.TypeIII.kloostermanCompactifiedDerivedOpenBaseChangeIso_hom
