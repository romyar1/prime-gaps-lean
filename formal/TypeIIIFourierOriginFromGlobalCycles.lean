import TypeIIIMiddleInfinityFromPerverse

/-!
# The finite-origin sequence on the perverse global Fourier transform

The general perverse cycle sequence is evaluated at the same global
Fourier object whose degree-minus-one restriction supplies the Fourier
sheaf. Its arrows are transported only by the canonical nearby/stalk
comparison. Laumon §2.3.2 supplies the general sequence; Proposition
2.3.2.1(iii), Lemma 2.4.2.1(ii) and Definition 2.4.2.3 supply the
general stationary-phase identification. These remain explicit laws.

Both closed terms have trivial geometric inertia, but no triviality of
arithmetic Frobenius is asserted. No cycle/base-change theorem for a
ramified normalization is assumed: normalization still restricts the
original representation sequence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace PrimeGap182.TypeIII.FourierOriginFromGlobalCycles
open PublishedPhaseApplication PublishedLocalConstruction SourceInverseImageSystem
open FiniteOriginFromRestriction NearbyFromStalkPullback TensorListRepresentation

universe mu t q w

/-- The original underlying equivariant map of a finite representation morphism. -/
abbrev intertwiner {G : Type mu} [Group G] {V W : FDRep ℂ G} (f : V ⟶ W) :
    Representation.IntertwiningMap V.ρ W.ρ :=
  ((forget₂ (FDRep ℂ G) (Rep ℂ G)).map f).hom

/-- Inflation of a geometric closed stalk, on its original linear maps. -/
def closedFunctor (G : Type mu) [Group G] : FGModuleCat ℂ ⥤ FDRep ℂ G where
  obj := geometricClosedStalk G
  map f := {
    hom := f
    comm := by intro g; change f ≫ 𝟙 _ = 𝟙 _ ≫ f; simp }

variable {K : Type} [Field K] (B : System.{0,mu} K)
  {I : Type t} [Group I] {G : Type mu} [Group G]
  (L : FiniteOriginFromRestriction.Data K ℂ I G)
  (J : B.Obj .parameter ⥤ FDRep ℂ G)
  {Q : Type q} [Category.{w} Q]
  (perverseInfinity : Q ⥤ FDRep ℂ I)

/-- General perverse local cycles at the finite origin, before a Fourier
object is selected. `closedMinusOne` and `closedZero` are H^-1 and H^0 of
the same closed restriction. The complete four-term sequence is retained.
Exactness at the middle two terms, injectivity and surjectivity are the
general perverse specialization sequence, not Type III conclusions. -/
structure Cycles (P : Type q) [Category.{w} P]
    (restriction : P ⥤ B.Obj .parameter) (raw : B.Obj .parameter ⥤ FDRep ℂ L.Raw) where
  nearby : P ⥤ FDRep ℂ L.Raw
  vanishing : P ⥤ FDRep ℂ L.Raw
  closedMinusOne : P ⥤ FGModuleCat ℂ
  closedZero : P ⥤ FGModuleCat ℂ
  stalkComparison : restriction ⋙ raw ≅ nearby
  specialize : closedMinusOne ⋙ closedFunctor L.Raw ⟶ nearby
  canonical : nearby ⟶ vanishing
  connecting : vanishing ⟶ closedZero ⋙ closedFunctor L.Raw
  injective : ∀ A, Function.Injective (intertwiner (specialize.app A)).toLinearMap
  exactNearby : ∀ A, LinearMap.range (intertwiner (specialize.app A)).toLinearMap =
    LinearMap.ker (intertwiner (canonical.app A)).toLinearMap
  exactVanishing : ∀ A, LinearMap.range (intertwiner (canonical.app A)).toLinearMap =
    LinearMap.ker (intertwiner (connecting.app A)).toLinearMap
  surjective : ∀ A, Function.Surjective (intertwiner (connecting.app A)).toLinearMap

/-- Shared one-dimensional perverse Fourier operation, its H^-1
restriction and the general finite-origin cycle laws. Stationary phase
identifies R^-1 Phi(Fourier P) with the local infinity-to-zero transform.
It applies to every perverse input in the continuous adic category, not
only the correlation family. No slope restriction is imposed here. -/
structure Inputs where
  Output : Type q
  [outputCategory : Category.{w} Output]
  transform : Q ⥤ Output
  restriction : Output ⥤ B.Obj .parameter
  stalk : StalkPullback B L J
  cycles : Cycles B L Output restriction stalk.raw
  infinity_admissible : ∀ P, L.Admissible (perverseInfinity.obj P)
  stationaryPhase : ∀ P, Representation.Equiv
    (cycles.vanishing.obj (transform.obj P)).ρ
    (L.unscaled.obj (perverseInfinity.obj P) (infinity_admissible P)).ρ

attribute [instance] Inputs.outputCategory

variable {B L J perverseInfinity} (S : Inputs B L J perverseInfinity)

/-- The punctured Fourier sheaf is the H^-1 restriction of this same
perverse global transform. -/
abbrev Inputs.fourier : Q ⥤ B.Obj .parameter := S.transform ⋙ S.restriction

/-- The original canonical cycle arrow, precomposed with the canonical
generic-stalk comparison; no independently chosen arrow is supplied. -/
def Inputs.toVanishing (P : Q) :
    Representation.IntertwiningMap (S.stalk.raw.obj (S.fourier.obj P)).ρ
      (S.cycles.vanishing.obj (S.transform.obj P)).ρ :=
  (intertwiner (S.cycles.canonical.app (S.transform.obj P))).comp
    (equivOfIso (S.cycles.stalkComparison.app (S.transform.obj P))).toIntertwiningMap

/-- The nearby comparison is invertible, so precomposition leaves the
image of the original cycle arrow unchanged. -/
theorem Inputs.exactness (P : Q) :
    LinearMap.range (S.toVanishing P).toLinearMap =
      LinearMap.ker (intertwiner (S.cycles.connecting.app (S.transform.obj P))).toLinearMap := by
  rw [← S.cycles.exactVanishing (S.transform.obj P)]
  ext y
  change (∃ x, intertwiner (S.cycles.canonical.app (S.transform.obj P))
      (equivOfIso (S.cycles.stalkComparison.app (S.transform.obj P)) x) = y) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨(equivOfIso (S.cycles.stalkComparison.app (S.transform.obj P))).symm x, ?_⟩
    simpa using hx

/-- Naturality of the transported original canonical arrow. -/
theorem Inputs.toVanishing_natural {P R : Q} (f : P ⟶ R) :
    S.stalk.raw.map (S.fourier.map f) ≫
        ((S.cycles.stalkComparison.app (S.transform.obj R)).hom ≫
          S.cycles.canonical.app (S.transform.obj R)) =
      ((S.cycles.stalkComparison.app (S.transform.obj P)).hom ≫
          S.cycles.canonical.app (S.transform.obj P)) ≫
        S.cycles.vanishing.map (S.transform.map f) := by
  have h := S.cycles.stalkComparison.hom.naturality (S.transform.map f)
  change S.stalk.raw.map (S.fourier.map f) ≫
      (S.cycles.stalkComparison.app (S.transform.obj R)).hom =
    (S.cycles.stalkComparison.app (S.transform.obj P)).hom ≫
      S.cycles.nearby.map (S.transform.map f) at h
  rw [← Category.assoc, h, Category.assoc,
    S.cycles.canonical.naturality (S.transform.map f), ← Category.assoc]

/-- The closed connecting arrow remains the original natural transformation. -/
theorem Inputs.connecting_natural {P R : Q} (f : P ⟶ R) :
    S.cycles.vanishing.map (S.transform.map f) ≫
        S.cycles.connecting.app (S.transform.obj R) =
      S.cycles.connecting.app (S.transform.obj P) ≫
        (S.cycles.closedZero ⋙ closedFunctor L.Raw).map (S.transform.map f) :=
  S.cycles.connecting.naturality (S.transform.map f)

/-- Assemble the former origin interface from the same perverse Fourier
object, cycle functors, arrows and general stationary-phase theorem. -/
def Inputs.originInputs : MiddleInfinityFromPerverse.OriginInputs B L J perverseInfinity where
  fourier := S.fourier
  stalk := S.stalk
  sequence := {
    infinity_admissible := S.infinity_admissible
    vanishing P := S.cycles.vanishing.obj (S.transform.obj P)
    closedStalk P := S.cycles.closedZero.obj (S.transform.obj P)
    nearbyToVanishing := S.toVanishing
    vanishingToClosed P := intertwiner (S.cycles.connecting.app (S.transform.obj P))
    localComparison := S.stationaryPhase
    exactness := S.exactness }

/-- The normalized finite-origin map uses the original canonical arrow
and the same stationary-phase and stalk comparisons, in this order. -/
theorem Inputs.normalized_toVanishing (a : PhaseField K) (ha : a ≠ 0) (P : Q) :
    ((S.originInputs.originData.cycles.normalized L).finiteOriginData.toVanishing a ha P).toLinearMap =
      (S.stationaryPhase P).toLinearMap.comp
        ((intertwiner (S.cycles.canonical.app (S.transform.obj P))).toLinearMap.comp
          (equivOfIso (S.cycles.stalkComparison.app (S.transform.obj P))).toLinearMap) := rfl

/-- The normalized outgoing map uses the original connecting arrow,
after the inverse of that same stationary-phase comparison. -/
theorem Inputs.normalized_toBoundary (a : PhaseField K) (ha : a ≠ 0) (P : Q) :
    ((S.originInputs.originData.cycles.normalized L).finiteOriginData.toBoundary a ha P).toLinearMap =
      (intertwiner (S.cycles.connecting.app (S.transform.obj P))).toLinearMap.comp
        (S.stationaryPhase P).symm.toLinearMap := rfl

end PrimeGap182.TypeIII.FourierOriginFromGlobalCycles

#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.closedFunctor
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.fourier
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.toVanishing
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.exactness
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.toVanishing_natural
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.connecting_natural
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.originInputs
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.normalized_toVanishing
#print axioms PrimeGap182.TypeIII.FourierOriginFromGlobalCycles.Inputs.normalized_toBoundary
