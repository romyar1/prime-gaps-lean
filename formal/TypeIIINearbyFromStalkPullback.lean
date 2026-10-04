import TypeIIIFiniteOriginFromRestriction
import TypeIIIFourierComparisonFromBaseChange

/-!
# The normalized nearby representation from the same global Fourier stalk

A general stalk/pullback law is applied only when the Laurent morphism
and the pointed local polynomial have identical coordinates. The concrete
frequency map satisfies both coefficient and coordinate conditions.
The unscaled cycle sequence begins literally at the raw generic stalk of
one global Fourier object. Thus its normalized nearby term is identified
with the pulled-back global stalk by the general law, not a separate
comparison for the completed Type III family.
The closed term is the geometric closed-point stalk, inflated from its
finite-dimensional vector space with trivial inertia. Laumon 2.3.2,
printed page 160, states that its action factors through residue Galois;
the geometric residue field here is algebraically closed. Its triviality
is therefore constructed, rather than supplied as a separate premise.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.NearbyFromStalkPullback

open PublishedPhaseApplication PublishedLocalConstruction PublishedPhysicalConstruction
open FiniteOriginFromRestriction FourierComparisonFromBaseChange FourierNormalizationMaps
open SourceInverseImageSystem GenericCurvePullback FourierSourceMaps GenericSourceSpecialization

universe mu t q v
variable {K : Type} [Field K]

/-- The global punctured-line map and the pointed local substitution
have exactly the same constant field and variable. Requiring an actual
Laurent ring homomorphism excludes polynomials that fail to map Gm to Gm. -/
structure CompatibleSubstitution (f : ParameterRing K →+* ParameterRing K)
    (q : PointedSubstitution (PhaseField K)) : Prop where
  constants : ∀ c, f (LaurentPolynomial.C c) = LaurentPolynomial.C c
  coordinate : f (LaurentPolynomial.T 1) = Polynomial.toLaurent q.polynomial

theorem normalization_compatible (s : (PhaseField K)ˣ) :
    CompatibleSubstitution (frequencyHom K s) (normalization s) where
  constants := frequencyHom_C K s
  coordinate := (normalization_frequency s).symm

/-- A stalk at a geometric closed point, viewed as an inertia representation.
This does not assert trivial arithmetic Frobenius at a closed point. -/
def geometricClosedStalk (G : Type mu) [Group G] (V : FGModuleCat ℂ) : FDRep ℂ G :=
  FDRep.of (Representation.trivial ℂ G V)

variable (B : System.{0,mu} K) {I : Type t} [Group I] {G : Type mu} [Group G]
  (L : FiniteOriginFromRestriction.Data K ℂ I G) (J : B.Obj .parameter ⥤ FDRep ℂ G)

/-- Generic geometric stalks as inertia representations. The rule is
for every sheaf and every compatible pointed substitution, before any
Fourier object or correlation is chosen. This is ordinary inverse-image
compatibility of a stalk, followed by restriction to wild inertia. -/
structure StalkPullback where
  raw : B.Obj .parameter ⥤ FDRep ℂ L.Raw
  pullback : ∀ (f : ParameterRing K →+* ParameterRing K)
    (q : PointedSubstitution (PhaseField K)), CompatibleSubstitution f q → ∀ A,
    restrict (L.localRestriction q) (raw.obj A) ≅
      J.obj ((B.pull (X := .parameter) (Y := .parameter)
        (Spec.map (CommRingCat.ofHom f))).obj A)

variable {Q : Type q}

/-- The unscaled published sequence with its first term fixed to the
generic Fourier stalk. There is no independently chosen nearby object. -/
structure CycleSequence (nearby : Q → FDRep ℂ L.Raw) where
  infinity : Q → FDRep ℂ I
  infinity_admissible : ∀ P, L.Admissible (infinity P)
  vanishing : Q → FDRep ℂ L.Raw
  closedStalk : Q → FGModuleCat ℂ
  nearbyToVanishing : ∀ P, Representation.IntertwiningMap (nearby P).ρ (vanishing P).ρ
  vanishingToClosed : ∀ P, Representation.IntertwiningMap (vanishing P).ρ
    (geometricClosedStalk L.Raw (closedStalk P)).ρ
  localComparison : ∀ P, Representation.Equiv (vanishing P).ρ
    (L.unscaled.obj (infinity P) (infinity_admissible P)).ρ
  exactness : ∀ P, LinearMap.range (nearbyToVanishing P).toLinearMap =
    LinearMap.ker (vanishingToClosed P).toLinearMap

section ClosedStalk
variable {L} {nearby : Q → FDRep ℂ L.Raw}

/-- The same closed-point vector space, with its actual geometric action. -/
def CycleSequence.closed (S : CycleSequence L nearby) (P : Q) : FDRep ℂ L.Raw :=
  geometricClosedStalk L.Raw (S.closedStalk P)

theorem CycleSequence.closedConstant (S : CycleSequence L nearby) (P : Q) :
    Representation.IsTrivial (S.closed P).ρ := by
  change Representation.IsTrivial (Representation.trivial ℂ L.Raw (S.closedStalk P))
  infer_instance

end ClosedStalk

/-- One Fourier object, the general stalk rule, and the cycle sequence
starting at that exact object's raw stalk, on the perverse domain Q. -/
structure OriginData (Q : Type q) where
  fourier : Q → B.Obj .parameter
  stalk : StalkPullback B L J
  sequence : CycleSequence L (fun P => stalk.raw.obj (fourier P))

variable {B L J} (O : OriginData B L J Q)

def OriginData.cycles : UnscaledCycles Q L.unscaled where
  infinity := O.sequence.infinity
  infinity_admissible := O.sequence.infinity_admissible
  nearby P := O.stalk.raw.obj (O.fourier P)
  vanishing := O.sequence.vanishing
  closed := O.sequence.closed
  nearbyToVanishing := O.sequence.nearbyToVanishing
  vanishingToClosed := O.sequence.vanishingToClosed
  localComparison := O.sequence.localComparison
  exactness := O.sequence.exactness
  closedConstant := O.sequence.closedConstant

/-- Apply the general stalk law at the proved compatible substitution.
The source is literally the normalized term of this same cycle sequence. -/
def OriginData.nearby (s : PhaseField K) (hs : s ≠ 0) (P : Q) :
    (O.cycles.normalized L).finiteOriginData.origin s hs P ≅
      J.obj ((B.pull (X := .parameter) (Y := .parameter)
        (frequencyMorphism K (Units.mk0 s hs))).obj (O.fourier P)) :=
  O.stalk.pullback (frequencyHom K (Units.mk0 s hs))
    (normalization (Units.mk0 s hs)) (normalization_compatible (Units.mk0 s hs)) (O.fourier P)

/-- The original unscaled arrow starts on that exact Fourier stalk. -/
theorem OriginData.nearbyToVanishing_linear (P : Q) :
    (O.cycles.nearbyToVanishing P).toLinearMap =
      (O.sequence.nearbyToVanishing P).toLinearMap := rfl

variable {Point : Type v} (D : CurveData (B.Obj .genericCurve) Point)
  (as : B.Obj .line) (middle : B.Obj .localCurve → Q)
  (affine : B.Obj .genericCurve ⥤ FDRep ℂ G)

/-- The remaining universal Fourier/cohomology laws on the very same
Fourier object. Its scaled nearby comparison is derived, not supplied. -/
structure CohomologyInputs where
  compactMiddle : B.Obj .genericCurve ⥤ B.Obj .parameter
  fiber : ∀ A, J.obj (compactMiddle.obj A) ≅ affine.obj A
  definition : ∀ A, O.fourier (middle A) ≅ compactMiddle.obj (universalInput B D as A)
  baseChange : ∀ (f : parameterScheme K ⟶ parameterScheme K)
    (g : genericScheme K ⟶ genericScheme K),
    IsPullback g (genericProjection K) (genericProjection K) f →
    g ≫ projectionMorphism K = projectionMorphism K → ∀ A,
    (B.pull (X := .parameter) (Y := .parameter) f).obj
      (compactMiddle.obj (universalInput B D as A)) ≅
      compactMiddle.obj ((B.pull (X := .genericCurve) (Y := .genericCurve) g).obj
        (universalInput B D as A))

variable {O D as middle affine}

/-- Fill the original comparison interface, retaining the global Fourier
object and all original cohomology maps. -/
def CohomologyInputs.comparisonInputs (C : CohomologyInputs O D as middle affine) :
    FourierComparisonFromBaseChange.Inputs B D as J middle
      (O.cycles.normalized L).finiteOriginData affine where
  fourier := O.fourier
  compactMiddle := C.compactMiddle
  fiber := C.fiber
  definition := C.definition
  baseChange := C.baseChange
  nearby := O.nearby

end PrimeGap182.TypeIII.NearbyFromStalkPullback

#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.normalization_compatible
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.geometricClosedStalk
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.CycleSequence.closed
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.CycleSequence.closedConstant
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.OriginData.cycles
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.OriginData.nearby
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.OriginData.nearbyToVanishing_linear
#print axioms PrimeGap182.TypeIII.NearbyFromStalkPullback.CohomologyInputs.comparisonInputs
