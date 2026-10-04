import TypeIIIScalarTraitFromLiteralPowerSeriesRescale02

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.TraitClosureLiftDifferenceFromEverySeries
open NativeWildRecognitionFromFixedGeometricTraits ScalarTraitFromLiteralPowerSeriesRescale
variable {E : Type} [Field E]

/-- The literal power-series embedding into the actual closure of its fraction field. -/
def seriesEmbedding : PowerSeries E →+* TraitClosure E :=
  (algebraMap (TraitFraction E) (TraitClosure E)).comp
    (algebraMap (PowerSeries E) (TraitFraction E))

@[simp] theorem closure_series_over (u : Eˣ) (f : PowerSeries E) :
    closureEquiv u (seriesEmbedding f) = seriesEmbedding (powerSeriesEquiv u f) := by
  change closureEquiv u
    (algebraMap (TraitFraction E) (TraitClosure E)
      (algebraMap (PowerSeries E) (TraitFraction E) f)) = _
  rw [closure_over, fraction_over]
  rfl


/-- Fixing EVERY embedded power series proves fixing the entire fraction field. -/
def fixingSeriesAutomorphism (a : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, a (seriesEmbedding f) = seriesEmbedding f) : TraitGroup E :=
  AlgEquiv.ofRingEquiv (f := a) (by
    intro z
    have he : a.toRingHom.comp (algebraMap (TraitFraction E) (TraitClosure E)) =
        algebraMap (TraitFraction E) (TraitClosure E) := by
      apply IsFractionRing.ringHom_ext (A := PowerSeries E)
      intro f
      exact h f
    exact RingHom.congr_fun he z)

@[simp] theorem fixingSeriesAutomorphism_apply
    (a : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, a (seriesEmbedding f) = seriesEmbedding f)
    (x : TraitClosure E) : fixingSeriesAutomorphism a h x = a x := rfl

/-- If two lifts agree on EVERY series, q1^-1*q2 is an actual trait Galois element. -/
def liftDifference (q1 q2 : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, q1 (seriesEmbedding f) = q2 (seriesEmbedding f)) : TraitGroup E :=
  fixingSeriesAutomorphism (q2.trans q1.symm) (by
    intro f
    change q1.symm (q2 (seriesEmbedding f)) = seriesEmbedding f
    rw [← h f, RingEquiv.symm_apply_apply])

@[simp] theorem liftDifference_action (q1 q2 : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, q1 (seriesEmbedding f) = q2 (seriesEmbedding f))
    (x : TraitClosure E) : q1 (liftDifference q1 q2 h x) = q2 x := by
  simp [liftDifference]

/-- The exact conjugation orientation needed by the finite-index covariance theorem. -/
theorem liftDifference_conjugacy (q1 q2 : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, q1 (seriesEmbedding f) = q2 (seriesEmbedding f))
    (g : TraitGroup E) (x : TraitClosure E) :
    q1.symm (g (q1 x)) =
      liftDifference q1 q2 h
        (q2.symm (g (q2 ((liftDifference q1 q2 h)⁻¹ x)))) := by
  simp [liftDifference, fixingSeriesAutomorphism, AlgEquiv.ofRingEquiv]

/-- The difference between an arbitrary genuine scalar lift and the computed lift. -/
def scalarLiftDifference (u : Eˣ) (a : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, a (seriesEmbedding f) = seriesEmbedding (powerSeriesEquiv u f)) :
    TraitGroup E :=
  liftDifference (closureEquiv u) a (by intro f; rw [closure_series_over, h f])

/-- Canonical and alternative scalar Galois maps differ by this computed inner element. -/
theorem scalarLift_conjugacy (u : Eˣ) (a : TraitClosure E ≃+* TraitClosure E)
    (h : ∀ f : PowerSeries E, a (seriesEmbedding f) = seriesEmbedding (powerSeriesEquiv u f))
    (g : TraitGroup E) (x : TraitClosure E) :
    a.symm (g (a x)) =
      ((scalarLiftDifference u a h)⁻¹ * inertiaEquiv u g * scalarLiftDifference u a h) x := by
  simp [scalarLiftDifference, liftDifference, fixingSeriesAutomorphism,
    inertiaEquiv, AlgEquiv.ofRingEquiv, AlgEquiv.mul_apply]

/-- The literal ALL-series square provides the equality of the two closure restrictions. -/
theorem powerScalar_series (q : TraitClosure E ≃+* TraitClosure E)
    (n : ℕ) (hn : n ≠ 0) (u : Eˣ)
    (hq : ∀ f : PowerSeries E, q (seriesEmbedding f) = seriesEmbedding (PowerSeries.expand n hn f))
    (f : PowerSeries E) :
    (q.trans (closureEquiv u)) (seriesEmbedding f) =
      ((closureEquiv (u ^ n)).trans q) (seriesEmbedding f) := by
  simp only [RingEquiv.trans_apply, hq, closure_series_over]
  exact congrArg seriesEmbedding (expand_rescale n hn u f)

/-- This actual Galois element compares power/scalar lifts; it is not a selected covariance law. -/
def powerScalarDifference (q : TraitClosure E ≃+* TraitClosure E)
    (n : ℕ) (hn : n ≠ 0) (u : Eˣ)
    (hq : ∀ f : PowerSeries E, q (seriesEmbedding f) = seriesEmbedding (PowerSeries.expand n hn f)) :
    TraitGroup E :=
  liftDifference (q.trans (closureEquiv u)) ((closureEquiv (u ^ n)).trans q)
    (powerScalar_series q n hn u hq)

/-- Contravariant pull on the actual trait group of an ALL-series power lift. -/
def powerGaloisHom (q : TraitClosure E ≃+* TraitClosure E)
    (n : ℕ) (hn : n ≠ 0)
    (hq : ∀ f : PowerSeries E, q (seriesEmbedding f) = seriesEmbedding (PowerSeries.expand n hn f)) :
    TraitGroup E →* TraitGroup E where
  toFun g := fixingSeriesAutomorphism (q.trans (g.toRingEquiv.trans q.symm)) (by
    intro f
    change q.symm (g (q (seriesEmbedding f))) = seriesEmbedding f
    rw [hq]
    have hg := g.commutes (algebraMap (PowerSeries E) (TraitFraction E)
      (PowerSeries.expand n hn f))
    change g (seriesEmbedding (PowerSeries.expand n hn f)) =
      seriesEmbedding (PowerSeries.expand n hn f) at hg
    rw [hg, ← hq f, RingEquiv.symm_apply_apply])
  map_one' := by ext x; simp [fixingSeriesAutomorphism, AlgEquiv.ofRingEquiv]
  map_mul' g h := by ext x; simp [fixingSeriesAutomorphism, AlgEquiv.ofRingEquiv, AlgEquiv.mul_apply]

@[simp] theorem powerGaloisHom_apply (q : TraitClosure E ≃+* TraitClosure E)
    (n : ℕ) (hn : n ≠ 0)
    (hq : ∀ f : PowerSeries E, q (seriesEmbedding f) = seriesEmbedding (PowerSeries.expand n hn f))
    (g : TraitGroup E) (x : TraitClosure E) :
    powerGaloisHom q n hn hq g x = q.symm (g (q x)) := rfl

/-- All factors and inverses are explicit; this is the closure-level compatibility to transport. -/
theorem powerScalar_conjugacy (q : TraitClosure E ≃+* TraitClosure E)
    (n : ℕ) (hn : n ≠ 0) (u : Eˣ)
    (hq : ∀ f : PowerSeries E, q (seriesEmbedding f) = seriesEmbedding (PowerSeries.expand n hn f))
    (g : TraitGroup E) (x : TraitClosure E) :
    q.symm ((inertiaEquiv u g) (q x)) =
      powerScalarDifference q n hn u hq
        ((inertiaEquiv (u ^ n)
          (powerGaloisHom q n hn hq g))
          ((powerScalarDifference q n hn u hq)⁻¹ x)) := by
  simpa [inertiaEquiv, AlgEquiv.ofRingEquiv, powerScalarDifference,
    fixingSeriesAutomorphism, powerGaloisHom] using
    liftDifference_conjugacy (q.trans (closureEquiv u))
      ((closureEquiv (u ^ n)).trans q) (powerScalar_series q n hn u hq) g x

end PrimeGap182.TypeIII.TraitClosureLiftDifferenceFromEverySeries
