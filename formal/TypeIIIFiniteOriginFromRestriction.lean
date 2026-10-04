import TypeIIIFiniteOriginFromVanishingCycles
import TypeIIIFourierNormalizationMaps

/-!
# One local Fourier functor and one sequence under normalized restriction

The published unscaled nearby/vanishing/closed sequence is restricted as
an exact sequence of representations. This does not assert that vanishing
cycles commute with ramified base change. All three terms, both arrows,
and the local Fourier output use the same homomorphism of inertia groups.
That homomorphism is obtained from a general pointed polynomial substitution,
instantiated at the actual polynomial T²/a of the Fourier normalization.

Admissibility remains the continuous finite-coefficient-field category of
Laumon §2.1.2. The unscaled functor, its additivity, the sequence, and the
geometric interpretation of local substitution are published-background
inputs. The normalized functor, sequence and maps are constructed below.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.FiniteOriginFromRestriction

open PublishedPhaseApplication PublishedLocalConstruction FourierNormalizationMaps
open PhysicalTorusLaurent GenericSourceSpecialization FourierSourceMaps SourceCurveBaseChange GenericCurvePullback

universe u v w t q

/-- A nonconstant local substitution fixing the origin. This is local
polynomial data, not a claim of a global endomorphism of the punctured line. -/
structure PointedSubstitution (k : Type u) [Field k] where
  polynomial : Polynomial k
  at_zero : polynomial.eval 0 = 0
  nonzero : polynomial ≠ 0

variable {K : Type u} [Field K]

/-- The same frequency coordinate as in the global Fourier comparison. -/
def normalization (s : (PhaseField K)ˣ) : PointedSubstitution (PhaseField K) where
  polynomial := Polynomial.X ^ 2 * Polynomial.C ((s : PhaseField K)⁻¹)
  at_zero := by simp
  nonzero := mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    (by simp)

/-- The pointed polynomial is exactly the previously checked Laurent
frequency coordinate, with the same nonzero scale. -/
theorem normalization_frequency (s : (PhaseField K)ˣ) :
    Polynomial.toLaurent (normalization s).polynomial =
      frequencyHom K s (LaurentPolynomial.T 1) := by
  simp only [normalization, map_mul, map_pow, Polynomial.toLaurent_X,
    Polynomial.toLaurent_C, frequencyHom, LaurentPolynomial.eval₂_T, zpow_one]
  change (LaurentPolynomial.T 1 : ParameterRing K) ^ 2 *
      LaurentPolynomial.C ((s : PhaseField K)⁻¹) =
    (((variableUnit (PhaseField K) ^ 2 / Units.map (LaurentPolynomial.C : PhaseField K →+* ParameterRing K).toMonoidHom s) :
      (ParameterRing K)ˣ) : ParameterRing K)
  change _ = (LaurentPolynomial.T 1 : ParameterRing K) ^ 2 *
    LaurentPolynomial.C ((s⁻¹ : (PhaseField K)ˣ) : PhaseField K)
  simp

variable {E : Type v} [Field E] {I : Type w} [Group I]
  {G H : Type t} [Group G] [Group H]

/-- Restriction changes the action, retaining the actual vector space. -/
def restrict (phi : G →* H) (V : FDRep E H) : FDRep E G :=
  FDRep.of (V.ρ.comp phi)

def restrictMap (phi : G →* H) {V W : FDRep E H}
    (f : Representation.IntertwiningMap V.ρ W.ρ) :
    Representation.IntertwiningMap (restrict phi V).ρ (restrict phi W).ρ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (phi g)

def restrictEquiv (phi : G →* H) {V W : FDRep E H}
    (e : Representation.Equiv V.ρ W.ρ) :
    Representation.Equiv (restrict phi V).ρ (restrict phi W).ρ where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' g := e.isIntertwining' (phi g)

/-- No flatness or base-change theorem is needed: the linear maps did not change. -/
theorem restrict_exact (phi : G →* H) {U V W : FDRep E H}
    (f : Representation.IntertwiningMap U.ρ V.ρ)
    (g : Representation.IntertwiningMap V.ρ W.ρ)
    (h : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap) :
    LinearMap.range (restrictMap phi f).toLinearMap =
      LinearMap.ker (restrictMap phi g).toLinearMap := h

theorem restrict_trivial (phi : G →* H) (V : FDRep E H)
    (h : Representation.IsTrivial V.ρ) : Representation.IsTrivial (restrict phi V).ρ := by
  let _ := h
  exact ⟨fun g => Representation.isTrivial_def V.ρ (phi g)⟩

def restrictSum (phi : G →* H) {ι : Type} [Fintype ι] (V : ι → FDRep E H) :
    Representation.Equiv (restrict phi (finiteSum V)).ρ
      (finiteSum (fun i => restrict phi (V i))).ρ where
  toLinearEquiv := LinearEquiv.refl E _
  isIntertwining' _ := by rfl

/-- Postcompose one admissible functor with actual representation restriction. -/
def restrictFunctor (phi : G →* H) {Admissible : FDRep E I → Prop}
    (F : AdmissibleRepresentationFunctor E I H Admissible) :
    AdmissibleRepresentationFunctor E I G Admissible where
  obj V hV := restrict phi (F.obj V hV)
  map _ _ f := restrictMap phi (F.map _ _ f)
  map_id V hV := by
    rw [F.map_id]
    rfl
  map_comp hU hV hW f g := by
    rw [F.map_comp]
    rfl

/-- Additivity of the single unscaled published local Fourier functor. -/
structure UnscaledAdditivity {Admissible : FDRep E I → Prop}
    (F : AdmissibleRepresentationFunctor E I H Admissible) where
  admissible_equiv : ∀ {R S : FDRep E I}, Representation.Equiv R.ρ S.ρ →
    Admissible R → Admissible S
  admissible_sum : ∀ {ι : Type} [Fintype ι], ∀ R : ι → FDRep E I,
    (∀ i, Admissible (R i)) → Admissible (finiteSum R)
  sum : ∀ {ι : Type} [Fintype ι], ∀ (R : ι → FDRep E I) (hR : ∀ i, Admissible (R i)),
    Representation.Equiv (F.obj (finiteSum R) (admissible_sum R hR)).ρ
      (finiteSum (fun i => F.obj (R i) (hR i))).ρ

/-- One unscaled output inertia group and Fourier functor. `localRestriction`
is the general pointed-substitution pullback followed by wild restriction,
with geometric points chosen compatibly. It has no Type III family input. -/
structure Data (K : Type u) [Field K] (E : Type v) [Field E]
    (I : Type w) [Group I] (G : Type t) [Group G] where
  Raw : Type t
  [rawGroup : Group Raw]
  localRestriction : PointedSubstitution (PhaseField K) → G →* Raw
  Admissible : FDRep E I → Prop
  unscaled : AdmissibleRepresentationFunctor E I Raw Admissible

attribute [instance] Data.rawGroup

variable (D : Data K E I G)

def Data.inertiaMap (a : PhaseField K) (ha : a ≠ 0) : G →* D.Raw :=
  D.localRestriction (normalization (Units.mk0 a ha))

def Data.normalized : LocalFourierData K E I G where
  Admissible := D.Admissible
  operation a ha := restrictFunctor (D.inertiaMap a ha) D.unscaled

/-- Every normalized direct-sum comparison comes from the same unscaled one. -/
def Data.additivity (F : UnscaledAdditivity D.unscaled) : LocalFourierAdditivity D.normalized where
  admissible_equiv := F.admissible_equiv
  admissible_sum := F.admissible_sum
  sum a ha _ _ R hR := (restrictEquiv (D.inertiaMap a ha) (F.sum R hR)).trans
    (restrictSum (D.inertiaMap a ha) (fun i => D.unscaled.obj (R i) (hR i)))

/-- Laumon's one unscaled perverse nearby/vanishing/closed sequence, together
with its canonical identification of the middle term as local Fourier. -/
structure UnscaledCycles (Q : Type q) {Admissible : FDRep E I → Prop}
    (F : AdmissibleRepresentationFunctor E I H Admissible) where
  infinity : Q → FDRep E I
  infinity_admissible : ∀ P, Admissible (infinity P)
  nearby : Q → FDRep E H
  vanishing : Q → FDRep E H
  closed : Q → FDRep E H
  nearbyToVanishing : ∀ P, Representation.IntertwiningMap (nearby P).ρ (vanishing P).ρ
  vanishingToClosed : ∀ P, Representation.IntertwiningMap (vanishing P).ρ (closed P).ρ
  localComparison : ∀ P, Representation.Equiv (vanishing P).ρ
    (F.obj (infinity P) (infinity_admissible P)).ρ
  exactness : ∀ P, LinearMap.range (nearbyToVanishing P).toLinearMap =
    LinearMap.ker (vanishingToClosed P).toLinearMap
  closedConstant : ∀ P, Representation.IsTrivial (closed P).ρ

variable {Q : Type q}

/-- Normalize the existing sequence of representations. The same restriction
map is applied to every term, arrow and the local Fourier comparison. -/
def UnscaledCycles.normalized (S : UnscaledCycles Q D.unscaled) :
    FiniteOriginFromVanishingCycles.Inputs Q D.normalized where
  infinity := S.infinity
  infinity_admissible := S.infinity_admissible
  nearby a ha P := restrict (D.inertiaMap a ha) (S.nearby P)
  vanishing a ha P := restrict (D.inertiaMap a ha) (S.vanishing P)
  closed a ha P := restrict (D.inertiaMap a ha) (S.closed P)
  nearbyToVanishing a ha P := restrictMap (D.inertiaMap a ha) (S.nearbyToVanishing P)
  vanishingToClosed a ha P := restrictMap (D.inertiaMap a ha) (S.vanishingToClosed P)
  localComparison a ha P := restrictEquiv (D.inertiaMap a ha) (S.localComparison P)
  exactness a ha P := restrict_exact (D.inertiaMap a ha)
    (S.nearbyToVanishing P) (S.vanishingToClosed P) (S.exactness P)
  closedConstant a ha P := restrict_trivial (D.inertiaMap a ha) (S.closed P) (S.closedConstant P)

/-- The finite-origin arrow is literally the unscaled composite as a linear
map; both its normalization and inertia equivariance were constructed. -/
theorem UnscaledCycles.toVanishing_linear (S : UnscaledCycles Q D.unscaled)
    (a : PhaseField K) (ha : a ≠ 0) (P : Q) :
    ((S.normalized D).finiteOriginData.toVanishing a ha P).toLinearMap =
      (S.localComparison P).toLinearMap.comp (S.nearbyToVanishing P).toLinearMap := rfl

theorem UnscaledCycles.toBoundary_linear (S : UnscaledCycles Q D.unscaled)
    (a : PhaseField K) (ha : a ≠ 0) (P : Q) :
    ((S.normalized D).finiteOriginData.toBoundary a ha P).toLinearMap =
      (S.vanishingToClosed P).toLinearMap.comp (S.localComparison P).symm.toLinearMap := rfl

end PrimeGap182.TypeIII.FiniteOriginFromRestriction

#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.normalization_frequency
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.restrict_exact
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.restrict_trivial
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.restrictFunctor
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.Data.additivity
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.UnscaledCycles.normalized
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.UnscaledCycles.toVanishing_linear
#print axioms PrimeGap182.TypeIII.FiniteOriginFromRestriction.UnscaledCycles.toBoundary_linear
