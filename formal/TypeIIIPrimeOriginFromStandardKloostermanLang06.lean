import TypeIIIStandardKloostermanLangOriginTheorems03
import TypeIIIOriginInvariantsSameFieldCommonConeBridge03
import TypeIIIPublishedOriginFrobenius

/-! Apply separate GENERAL primitive theorems using individual curve-object
realization isomorphisms. Every Weil square is derived from B.originWeil's
SAME naturality, not an extra native Frobenius recognition. This computes the
two prime-field primitive laws only; finite extension/scalar/Tate rules and
the complete original originActions record are not supplied or claimed.

The AS object comparison must identify native Lang F-1 with character psi^-1
against the standard Lang 1-F associated sheaf with character psi. This exact
sign convention is part of the individual source-object realization, never
deduced for arbitrary native artinSchreier choices. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.PrimeOriginFromStandardKloostermanLang
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open StandardKloostermanLangOrigin OriginStalksFromStandardWeilInvariants
open ExactInverseImagesToDerived RationalPointStalksFromUniversalFiber
open ArithmeticSourceMaps StartingSourceMaps
universe nu mu g
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C) (F : ArithmeticFibers C)
  (nativeCompact : ∀ (E : Type) [Field E] [Fintype E] (_h2 : (2 : E) ≠ 0),
    Fin 3 → C (fiberScheme E) ⥤ C (Spec (.of E)))
  {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (D : FaithfulArithmeticOperations C U F nativeCompact S)
  (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)

/-- Map only an individual curve-object realization through SAME origin. -/
def curveCoefficientIso (A : C (affineLine K)) (Q : S.Curve K h2)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅ Q) :
    (B.origin K h2).obj ((D.curveRealization K h2).obj
      ((U.pull (localInputMorphism K K)).obj A)) ≅ (B.origin K h2).obj Q :=
  (B.origin K h2).mapIso e

def curveInvariantIso (A : C (affineLine K)) (Q : S.Curve K h2)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅ Q) :
    (originStalks C U F nativeCompact B D K K h2).fiber A ≃ₗ[ℂ]
      (invariantStalks (B.origin K h2) (B.originConjugation K h2)
        (B.originWeil K h2)).fiber Q :=
  ((Rep.invariantsFunctor ℂ (B.OriginGroup K h2)).mapIso
    ((forget₂ (FDRep ℂ (B.OriginGroup K h2)) (Rep ℂ (B.OriginGroup K h2))).mapIso
      (curveCoefficientIso C U F nativeCompact B D K h2 A Q e))).toLinearEquiv

@[simp] theorem curveInvariantIso_val (A : C (affineLine K)) (Q : S.Curve K h2)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅ Q)
    (x : (originStalks C U F nativeCompact B D K K h2).fiber A) :
    (curveInvariantIso C U F nativeCompact B D K h2 A Q e x).val =
      (curveCoefficientIso C U F nativeCompact B D K h2 A Q e).hom.hom.hom x.val := rfl

/-- ALL-Weil commutation follows from an arithmetic curve morphism. -/
theorem curveCoefficientIso_weil (A : C (affineLine K)) (Q : S.Curve K h2)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅ Q)
    (w : (B.originWeil K h2).Weil)
    (x : ((B.origin K h2).obj ((D.curveRealization K h2).obj
      ((U.pull (localInputMorphism K K)).obj A))).V) :
    (curveCoefficientIso C U F nativeCompact B D K h2 A Q e).hom.hom.hom
      ((B.originWeil K h2).representation
        ((D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A)) w x) =
    (B.originWeil K h2).representation Q w
      ((curveCoefficientIso C U F nativeCompact B D K h2 A Q e).hom.hom.hom x) :=
  (B.originWeil K h2).natural e.hom w x

theorem curveInvariantIso_frobenius (A : C (affineLine K)) (Q : S.Curve K h2)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅ Q)
    (x : (originStalks C U F nativeCompact B D K K h2).fiber A) :
    curveInvariantIso C U F nativeCompact B D K h2 A Q e
      ((originStalks C U F nativeCompact B D K K h2).frobenius A x) =
    (invariantStalks (B.origin K h2) (B.originConjugation K h2)
      (B.originWeil K h2)).frobenius Q
        (curveInvariantIso C U F nativeCompact B D K h2 A Q e x) := by
  apply Subtype.ext
  exact curveCoefficientIso_weil C U F nativeCompact B D K h2 A Q e
    (B.originWeil K h2).frobenius x.val

variable (P : StandardKloostermanLangOrigin.Operations S B)
  {interpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    StandardKloostermanLangOrigin.Operations S B → Prop}
  (published : StandardKloostermanLangOrigin.PublishedTheorems interpretation)
  (model : interpretation S B P)

include published model in
/-- Native raw Kl3 invariant action from Katz's ALL-rank standard theorem.
The MODEL operand is only the source-object Iso, never an invariant action. -/
theorem raw_frobenius (A : C (affineLine K)) (psi : AddChar K (PadicAlgCl 2))
    (hpsi : psi ≠ 1)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅
      P.rawKloosterman K h2 3 psi)
    (x : (originStalks C U F nativeCompact B D K K h2).fiber A) :
    (originStalks C U F nativeCompact B D K K h2).frobenius A x = x := by
  apply (curveInvariantIso C U F nativeCompact B D K h2 A _ e).injective
  rw [curveInvariantIso_frobenius]
  exact StandardKloostermanLangOrigin.raw_invariant_frobenius B P K h2 published model
    3 (by decide) psi hpsi _

include published model in
/-- Native Lang AS action at zero from the ALL-point formula, lissity and
ordinary stalk/inertia comparison. No full nearby scalar identity is input. -/
theorem artinSchreier_frobenius (A : C (affineLine K)) (psi : AddChar K (PadicAlgCl 2))
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅
      (P.restriction K h2).obj (P.langAS K h2 psi))
    (x : (originStalks C U F nativeCompact B D K K h2).fiber A) :
    (originStalks C U F nativeCompact B D K K h2).frobenius A x = x := by
  apply (curveInvariantIso C U F nativeCompact B D K h2 A _ e).injective
  rw [curveInvariantIso_frobenius]
  exact StandardKloostermanLangOrigin.lang_invariant_frobenius B P K h2 published model psi _

include published model in
/-- Exact two original prime primitive action targets, using literal projections
of PublishedPrimitiveSources.Data. This is not the complete Rules record. -/
theorem prime_raw (p : ℕ) [Fact p.Prime]
    (primitive : PublishedPrimitiveSources.Data p (C (affineLine (ZMod p))))
    (h2p : (2 : ZMod p) ≠ 0) (psi : AddChar (ZMod p) (PadicAlgCl 2))
    (hpsi : psi ≠ 1)
    (e : (D.curveRealization (ZMod p) h2p).obj
      ((U.pull (localInputMorphism (ZMod p) (ZMod p))).obj (primitive.kloosterman3 psi)) ≅
      P.rawKloosterman (ZMod p) h2p 3 psi) :
    (originStalks C U F nativeCompact B D (ZMod p) (ZMod p) h2p).frobenius
      (primitive.kloosterman3 psi) = 1 := by
  ext x
  exact raw_frobenius C U F nativeCompact B D (ZMod p) h2p P published model _ psi hpsi e x

include published model in
theorem prime_artinSchreier (p : ℕ) [Fact p.Prime]
    (primitive : PublishedPrimitiveSources.Data p (C (affineLine (ZMod p))))
    (h2p : (2 : ZMod p) ≠ 0) (psi : AddChar (ZMod p) (PadicAlgCl 2))
    (e : (D.curveRealization (ZMod p) h2p).obj
      ((U.pull (localInputMorphism (ZMod p) (ZMod p))).obj (primitive.artinSchreier psi)) ≅
      (P.restriction (ZMod p) h2p).obj (P.langAS (ZMod p) h2p psi)) :
    (originStalks C U F nativeCompact B D (ZMod p) (ZMod p) h2p).frobenius
      (primitive.artinSchreier psi) = 1 := by
  ext x
  exact artinSchreier_frobenius C U F nativeCompact B D (ZMod p) h2p P published model _ psi e x

include published model in
/-- Transport through the gated SAME-field common group comparison. The group
universe g stays arbitrary; no group-dictionary existence is inferred. -/
theorem common_raw_frobenius
    (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
    (A : C (affineLine K)) (psi : AddChar K (PadicAlgCl 2)) (hpsi : psi ≠ 1)
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅
      P.rawKloosterman K h2 3 psi)
    (x : (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K K h2).fiber A) :
    (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K K h2).frobenius A x = x := by
  apply (OriginInvariantsSameFieldCommonConeBridge.commonInvariantComparison.{g,nu,mu}
    C U F nativeCompact B D originTrait K K h2 A).injective
  rw [OriginInvariantsSameFieldCommonConeBridge.common_frobenius_square]
  exact raw_frobenius C U F nativeCompact B D K h2 P published model A psi hpsi e _

include published model in
/-- The same common-group transport for native Lang AS; sign is still the
individual source-object realization, not an inferred arbitrary-model law. -/
theorem common_artinSchreier_frobenius
    (originTrait : NativeCommonArithmeticTraitWeilCone.OriginTraitDictionary S B)
    (A : C (affineLine K)) (psi : AddChar K (PadicAlgCl 2))
    (e : (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj A) ≅
      (P.restriction K h2).obj (P.langAS K h2 psi))
    (x : (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K K h2).fiber A) :
    (OriginInvariantsSameFieldCommonConeBridge.commonOriginStalks.{g,nu,mu}
      C U F nativeCompact B D originTrait K K h2).frobenius A x = x := by
  apply (OriginInvariantsSameFieldCommonConeBridge.commonInvariantComparison.{g,nu,mu}
    C U F nativeCompact B D originTrait K K h2 A).injective
  rw [OriginInvariantsSameFieldCommonConeBridge.common_frobenius_square]
  exact artinSchreier_frobenius C U F nativeCompact B D K h2 P published model A psi e _

/-- Honest individual before-prime MODEL recognition: ALL finite K, literal
source objects, SAME local-input pull and curve realization. The native AS
construction's F-1/psi^-1 sign is identified against standard 1-F/psi here. -/
structure UniversalPrimitiveCurveRecognition
    (nativeRaw nativeAS : ∀ (K : Type) [Field K] [Fintype K] (_h2 : (2 : K) ≠ 0),
      AddChar K (PadicAlgCl 2) → C (affineLine K)) where
  raw : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (_hpsi : psi ≠ 1),
    (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj
      (nativeRaw K h2 psi)) ≅ P.rawKloosterman K h2 3 psi
  artinSchreier : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (psi : AddChar K (PadicAlgCl 2)) (_hpsi : psi ≠ 1),
    (D.curveRealization K h2).obj ((U.pull (localInputMorphism K K)).obj
      (nativeAS K h2 psi)) ≅ (P.restriction K h2).obj (P.langAS K h2 psi)

end PrimeGap182.TypeIII.PrimeOriginFromStandardKloostermanLang
