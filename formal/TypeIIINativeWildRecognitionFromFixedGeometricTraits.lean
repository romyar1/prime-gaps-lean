import TypeIIINativePointFiberFromUniversalGeometricFibers
import TypeIIIFiniteRepresentationCoefficientTransport
import TypeIIINativePunctualZeroPhaseFromActualPointWitnesses
import Mathlib.RingTheory.PowerSeries.Basic

/-!
Fixed genuine geometric trait fibers, rather than an arbitrary retained W,
are the domains of the general lisse/unramified/rank theorem. Every trait is
literally Spec E[[T]], with native fraction field, algebraic closure and its
actual field automorphism group. The intended wild subgroup, continuous
finite-coefficient realization and generic acted fiber are fixed general
MODEL DATA before a prime. No target triviality/rank is used to define their
recognition predicate.

An explicit selected group/functor alignment to SAME W transfers the two
consequences. The actual positive-T/closed-zero square and a general
compatible coefficient-fiber inverse-image dictionary supply the point rank.
This is conditional MODEL/theorem application, not an adic construction or
an unconditional citation match for arbitrary ordinary C.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical PrimeGap182.TypeIII.TwoAdicComplexEmbedding
namespace PrimeGap182.TypeIII.NativeWildRecognitionFromFixedGeometricTraits
open ExactInverseImagesToDerived CanonicalPrimeFramework
open LinearRadialPhaseFromPoleTransport OriginPoleFromExactInverseImages
open NativePointFiberFromUniversalGeometricFibers NativePunctualFourierFromLisseWildStalks
open FiniteRepresentationCoefficientTransport PublishedPhaseApplication NativeSurfaceFromGeometricStalks

abbrev traitScheme (E : Type) [Field E] : Scheme := Spec (.of (PowerSeries E))
abbrev TraitFraction (E : Type) [Field E] := FractionRing (PowerSeries E)
abbrev TraitClosure (E : Type) [Field E] := AlgebraicClosure (TraitFraction E)
abbrev TraitGroup (E : Type) [Field E] := TraitClosure E ≃ₐ[TraitFraction E] TraitClosure E

/-- The positive parameter map, with native constants and T. -/
def parameterMap (E : Type) [Field E] : traitScheme E ⟶ Spec (.of (Polynomial E)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom PowerSeries.C PowerSeries.X))
def closedPoint (E : Type) [Field E] : Spec (.of E) ⟶ traitScheme E :=
  Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff)
def affineZero (E : Type) [Field E] : Spec (.of E) ⟶ Spec (.of (Polynomial E)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : E)))

theorem closedPoint_parameter (E : Type) [Field E] :
    closedPoint E ≫ parameterMap E = affineZero E := by
  dsimp only [closedPoint,parameterMap,affineZero]
  rw [← Spec.map_comp,← CommRingCat.ofHom_comp]
  apply congrArg (fun h => Spec.map (CommRingCat.ofHom h))
  apply Polynomial.ringHom_ext
  · intro c
    simp
  · simp

universe mu g
variable (C : Scheme → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme => X) C)
  (Lisse : ∀ X : Scheme, C X → Prop)
  (pointFibers : GeometricFibers C)

/-- General genuine geometric acted fibers on the actual power-series traits.
FiniteContinuous selects the intended finite-coefficient continuous adic
realization; it is not defined by rank, action triviality or a TypeIII target.
Wild is the separately recognized geometric wild subgroup of actual field
closure automorphisms. No selected W occurs in this DATA. -/
structure GeometricTraitFibers where
  genericFiber : ∀ (E : Type) [Field E] [IsAlgClosed E],
    C (traitScheme E) ⥤ FDRep (PadicAlgCl 2) (TraitGroup E)
  FiniteContinuous : ∀ (E : Type) [Field E] [IsAlgClosed E], C (traitScheme E) → Prop
  wild : ∀ (E : Type) [Field E] [IsAlgClosed E], Subgroup (TraitGroup E)

variable (traits : GeometricTraitFibers C)

/-- General strict-henselian lisse realization, with valid ell=2 scope.
The acted generic fiber is the fixed genuine trait fiber, never arbitrary W. -/
structure UniversalLisseTraitRealization : Prop where
  recognized : ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E] [CharP E p]
    (_h2 : (2 : E) ≠ 0) F, Lisse (traitScheme E) F → traits.FiniteContinuous E F
  unramified : ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E] [CharP E p]
    (_h2 : (2 : E) ≠ 0) F, Lisse (traitScheme E) F → traits.FiniteContinuous E F →
      Representation.IsTrivial ((traits.genericFiber E).obj F).ρ
  rank : ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E] [CharP E p]
    (_h2 : (2 : E) ≠ 0) F, Lisse (traitScheme E) F → traits.FiniteContinuous E F →
      Module.finrank (PadicAlgCl 2) ((traits.genericFiber E).obj F) =
        Module.finrank ℂ ((pointFibers.fiber E).obj ((U.pull (closedPoint E)).obj F))

/-- Compatible geometric coefficient-point inverse image, on ALL valid
algebraically closed field maps. The choice of compatible geometric fibers
is explicit MODEL coherence, not a rank equality on a selected object. -/
abbrev CoefficientFiberInverseImage :=
  ∀ (p : ℕ) [Fact p.Prime] (E B : Type) [Field E] [IsAlgClosed E] [CharP E p]
    [Field B] [IsAlgClosed B] [CharP B p] (_h2E : (2 : E) ≠ 0) (_h2B : (2 : B) ≠ 0)
    (a : E →+* B), U.pull (Spec.map (CommRingCat.ofHom a)) ⋙ pointFibers.fiber B ≅
      pointFibers.fiber E

/-- Literal fixed coefficient transport and actual group restriction. -/
def traitWildFiber (E : Type) [Field E] [IsAlgClosed E] {G : Type g} [Group G]
    (embedding : G →* traits.wild E) : C (traitScheme E) ⥤ FDRep ℂ G :=
  traits.genericFiber E ⋙ (coefficientEquivalence TwoAdicComplexEmbedding.complexEquiv
    (TraitGroup E)).functor ⋙ Action.res (FGModuleCat ℂ)
      ((traits.wild E).subtype.comp embedding)

def originModel (E : Type) [Field E] [IsAlgClosed E] {G : Type g} [Group G]
    (embedding : G →* traits.wild E) : C (Spec (.of (Polynomial E))) ⥤ FDRep ℂ G :=
  U.pull (parameterMap E) ⋙ traitWildFiber C traits E embedding

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) F, Lisse Y F → Lisse X ((U.pull f).obj F))
  (realization : UniversalLisseTraitRealization C U Lisse pointFibers traits)
  (coefficientInverseImage : CoefficientFiberInverseImage C U pointFibers)
  (p : ℕ) [Fact p.Prime]
  (h2Phi : (2 : AlgebraicClosure (ZMod p)) ≠ 0)
  (h2E : (2 : PhaseField (AlgebraicClosure (ZMod p))) ≠ 0)
  {G : Type g} [Group G]
  (W : OrdinaryWild (E := ℂ) (G := G) (primeCommon C U p))
  (embedding : G →* traits.wild (PhaseField (AlgebraicClosure (ZMod p))))
  (alignment : W.originWild ≅ originModel C U traits
    (PhaseField (AlgebraicClosure (ZMod p))) embedding)

include realization lissePull h2E alignment in
/-- The retained SAME-W unramified consequence is derived via the genuine model. -/
theorem recognizedWildUnramified
    (f : originScheme (AlgebraicClosure (ZMod p)) ⟶
      FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)))
    (F : C (FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p))))
    (hF : Lisse _ F) :
    Representation.IsTrivial
      (W.originWild.obj ((U.pull f).obj F)).ρ := by
  let E := PhaseField (AlgebraicClosure (ZMod p))
  let T := (U.pull (parameterMap E)).obj ((U.pull f).obj F)
  have hL : Lisse (traitScheme E) T := lissePull _ _ (lissePull _ _ hF)
  let := realization.unramified p E h2E T hL (realization.recognized p E h2E T hL)
  have hOp : ∀ g, ((coefficientEquivalence TwoAdicComplexEmbedding.complexEquiv
      (TraitGroup E)).functor.obj ((traits.genericFiber E).obj T)).ρ g = 1 :=
    (trivialAction_iff TwoAdicComplexEmbedding.complexEquiv (TraitGroup E) _).mpr
      (fun g => Representation.isTrivial_def _ g)
  let R := (traitWildFiber C traits E embedding).obj T
  let : Representation.IsTrivial R.ρ := ⟨fun g => hOp _⟩
  let e := alignment.app ((U.pull f).obj F)
  constructor
  intro g
  have hR : Representation.IsTrivial
      ((originModel C U traits E embedding).obj ((U.pull f).obj F)).ρ := by
    change Representation.IsTrivial R.ρ
    infer_instance
  rw [FDRep.Iso.conj_ρ e.symm,hR.out g]
  simp

include realization lissePull coefficientInverseImage h2Phi h2E alignment in
/-- The original point-rank consequence follows from actual closed-point maps. -/
theorem recognizedWildRank
    (f : originScheme (AlgebraicClosure (ZMod p)) ⟶
      FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)))
    (F : C (FullFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p))))
    (hF : Lisse _ F)
    (hf : originZero (AlgebraicClosure (ZMod p)) ≫ f =
      originBasePoint (AlgebraicClosure (ZMod p)) ≫
        pointMorphism (AlgebraicClosure (ZMod p)) (0,0)) :
    Module.finrank ℂ (W.originWild.obj ((U.pull f).obj F)) =
      Module.finrank ℂ ((planeFiberZero (A := primeCommon C U p)
        NativeAuxiliarySchemes.Space.geometricPoint rfl
        (nativePointFiber C pointFibers p)).obj F) := by
  let E := PhaseField (AlgebraicClosure (ZMod p))
  let T := (U.pull (parameterMap E)).obj ((U.pull f).obj F)
  have hL : Lisse (traitScheme E) T := lissePull _ _ (lissePull _ _ hF)
  let e := alignment.app ((U.pull f).obj F)
  calc
    Module.finrank ℂ (W.originWild.obj ((U.pull f).obj F)) =
        Module.finrank ℂ ((traitWildFiber C traits E embedding).obj T) := (FDRep.isoToLinearEquiv e).finrank_eq
    _ = Module.finrank (PadicAlgCl 2) ((traits.genericFiber E).obj T) :=
      finrank_eq TwoAdicComplexEmbedding.complexEquiv (TraitGroup E) _
    _ = Module.finrank ℂ ((pointFibers.fiber E).obj ((U.pull (closedPoint E)).obj T)) :=
      realization.rank p E h2E T hL (realization.recognized p E h2E T hL)
    _ = Module.finrank ℂ ((planeFiberZero (A := primeCommon C U p)
        NativeAuxiliarySchemes.Space.geometricPoint rfl (nativePointFiber C pointFibers p)).obj F) := by
      let zero := originZero (AlgebraicClosure (ZMod p))
      let base := originBasePoint (AlgebraicClosure (ZMod p))
      let point := pointMorphism (AlgebraicClosure (ZMod p)) (0,0)
      let eMaps : U.pull f ⋙ U.pull (parameterMap E) ⋙ U.pull (closedPoint E) ≅
          U.pull point ⋙ U.pull base :=
        Functor.isoWhiskerLeft (U.pull f)
          (U.composition (closedPoint E) (parameterMap E) ≪≫
            eqToIso (congrArg (fun g => U.pull g) (closedPoint_parameter E))) ≪≫
        U.composition zero f ≪≫ eqToIso (congrArg (fun g => U.pull g) hf) ≪≫
        (U.composition base point).symm
      let eCoef := coefficientInverseImage p (AlgebraicClosure (ZMod p)) E h2Phi h2E
        (algebraMap (AlgebraicClosure (ZMod p)) E)
      let eClosed := Functor.isoWhiskerRight eMaps (pointFibers.fiber E) ≪≫
        Functor.associator (U.pull point) (U.pull base) (pointFibers.fiber E) ≪≫
        Functor.isoWhiskerLeft (U.pull point) eCoef
      exact (eClosed.app F).toLinearEquiv.finrank_eq
end PrimeGap182.TypeIII.NativeWildRecognitionFromFixedGeometricTraits
