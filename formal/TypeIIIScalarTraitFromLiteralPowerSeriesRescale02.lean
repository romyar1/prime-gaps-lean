import TypeIIINativeWildRecognitionFromFixedGeometricTraits
import Mathlib.RingTheory.PowerSeries.Expand

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PrimeGap182.TypeIII.ScalarTraitFromLiteralPowerSeriesRescale
open NativeWildRecognitionFromFixedGeometricTraits

variable {E : Type} [Field E]

/-- The literal ALL-series scalar substitution, with its literal inverse. -/
def powerSeriesEquiv (u : Eˣ) : PowerSeries E ≃+* PowerSeries E where
  toFun := PowerSeries.rescale (u : E)
  invFun := PowerSeries.rescale ((u⁻¹ : Eˣ) : E)
  left_inv f := by simp [PowerSeries.rescale_rescale]
  right_inv f := by simp [PowerSeries.rescale_rescale]
  map_mul' := (PowerSeries.rescale (u : E)).map_mul
  map_add' := (PowerSeries.rescale (u : E)).map_add

@[simp] theorem powerSeriesEquiv_C (u : Eˣ) (c : E) :
    powerSeriesEquiv u (PowerSeries.C c) = PowerSeries.C c := by
  change PowerSeries.rescale (u : E) (PowerSeries.C c) = PowerSeries.C c
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst n; simp
  · simp

@[simp] theorem powerSeriesEquiv_X (u : Eˣ) :
    powerSeriesEquiv u PowerSeries.X = PowerSeries.C (u : E) * PowerSeries.X :=
  PowerSeries.rescale_X (u : E)

/-- The actual fraction-ring scalar map. -/
def fractionEquiv (u : Eˣ) : TraitFraction E ≃+* TraitFraction E :=
  IsFractionRing.ringEquivOfRingEquiv (K := TraitFraction E) (L := TraitFraction E)
    (powerSeriesEquiv u)

@[simp] theorem fraction_over (u : Eˣ) (f : PowerSeries E) :
    fractionEquiv u (algebraMap (PowerSeries E) (TraitFraction E) f) =
      algebraMap (PowerSeries E) (TraitFraction E) (powerSeriesEquiv u f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (powerSeriesEquiv u) f

/-- A coefficient-compatible algebraic-closure lift, chosen by existing uniqueness. -/
def closureEquiv (u : Eˣ) : TraitClosure E ≃+* TraitClosure E :=
  IsAlgClosure.equivOfEquiv (TraitClosure E) (TraitClosure E) (fractionEquiv u)

@[simp] theorem closure_over (u : Eˣ) (f : TraitFraction E) :
    closureEquiv u (algebraMap (TraitFraction E) (TraitClosure E) f) =
      algebraMap (TraitFraction E) (TraitClosure E) (fractionEquiv u f) :=
  IsAlgClosure.equivOfEquiv_algebraMap (TraitClosure E) (TraitClosure E) (fractionEquiv u) f

@[simp] theorem closure_symm_over (u : Eˣ) (f : TraitFraction E) :
    (closureEquiv u).symm (algebraMap (TraitFraction E) (TraitClosure E) f) =
      algebraMap (TraitFraction E) (TraitClosure E) ((fractionEquiv u).symm f) :=
  IsAlgClosure.equivOfEquiv_symm_algebraMap (TraitClosure E) (TraitClosure E) (fractionEquiv u) f

/-- The actual contravariant scalar Galois map g ↦ q^-1*g*q. -/
def inertiaEquiv (u : Eˣ) : TraitGroup E ≃* TraitGroup E where
  toFun g := AlgEquiv.ofRingEquiv
    (f := (closureEquiv u).trans (g.toRingEquiv.trans (closureEquiv u).symm))
    (by intro f; simp only [RingEquiv.trans_apply, closure_over, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, closure_symm_over, RingEquiv.symm_apply_apply])
  invFun g := AlgEquiv.ofRingEquiv
    (f := (closureEquiv u).symm.trans (g.toRingEquiv.trans (closureEquiv u)))
    (by intro f; simp only [RingEquiv.trans_apply, closure_symm_over, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, closure_over, RingEquiv.apply_symm_apply])
  left_inv g := by ext x; simp [AlgEquiv.ofRingEquiv]
  right_inv g := by ext x; simp [AlgEquiv.ofRingEquiv]
  map_mul' g h := by ext x; simp [AlgEquiv.ofRingEquiv, AlgEquiv.mul_apply]

@[simp] theorem action_coherence (u : Eˣ) (g : TraitGroup E) (x : TraitClosure E) :
    closureEquiv u (inertiaEquiv u g x) = g (closureEquiv u x) := by
  simp [inertiaEquiv, AlgEquiv.ofRingEquiv]

/-- The literal ALL-power-series power/scalar square; no continuity or
geometric fiber interpretation is needed to prove it. -/
theorem expand_rescale (n : ℕ) (hn : n ≠ 0) (u : Eˣ) (f : PowerSeries E) :
    powerSeriesEquiv u (PowerSeries.expand n hn f) =
      PowerSeries.expand n hn (powerSeriesEquiv (u ^ n) f) := by
  change PowerSeries.rescale (u : E) (PowerSeries.expand n hn f) =
    PowerSeries.expand n hn (PowerSeries.rescale ((u ^ n : Eˣ) : E) f)
  ext m
  by_cases h : n ∣ m
  · obtain ⟨l,rfl⟩ := h
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_expand_mul,
      Units.val_pow_eq_pow_val, pow_mul]
  · simp only [PowerSeries.coeff_rescale,
      PowerSeries.coeff_expand_of_not_dvd n hn _ h, mul_zero]

end PrimeGap182.TypeIII.ScalarTraitFromLiteralPowerSeriesRescale
