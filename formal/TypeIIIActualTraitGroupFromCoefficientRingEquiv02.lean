import TypeIIITraitClosureLiftDifferenceFromEverySeries04
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Pure coefficient transport on the literal formal trait fraction fields,
algebraic closures and their base-field automorphism groups. The coefficient
field equivalence is genuine and bijective, and the positive parameter stays X.
No native/standard realization, topology, finite-field choice or model existence
is supplied. The algebraic closure extension is a choice; its inverse below is
the SAME chosen inverse, not a separately chosen extension of the inverse map. -/
noncomputable section
namespace PrimeGap182.TypeIII.ActualTraitGroupFromCoefficientRingEquiv
open NativeWildRecognitionFromFixedGeometricTraits
open TraitClosureLiftDifferenceFromEverySeries

variable {E F : Type} [Field E] [Field F] (a : E ≃+* F)

/-- Coefficient transport, without changing the positive formal parameter. -/
def seriesEquiv : PowerSeries E ≃+* PowerSeries F :=
  { PowerSeries.map a.toRingHom with
    invFun := PowerSeries.map a.symm.toRingHom
    left_inv := by
      intro f
      ext j
      change a.symm (a (f.coeff j)) = f.coeff j
      exact a.symm_apply_apply _
    right_inv := by
      intro f
      ext j
      change a (a.symm (f.coeff j)) = f.coeff j
      exact a.apply_symm_apply _ }

@[simp] theorem seriesEquiv_coeff (f : PowerSeries E) (j : ℕ) :
    (seriesEquiv a f).coeff j = a (f.coeff j) := rfl

@[simp] theorem seriesEquiv_symm_coeff (f : PowerSeries F) (j : ℕ) :
    ((seriesEquiv a).symm f).coeff j = a.symm (f.coeff j) := rfl

@[simp] theorem seriesEquiv_parameter :
    seriesEquiv a (PowerSeries.X : PowerSeries E) = (PowerSeries.X : PowerSeries F) :=
  PowerSeries.map_X a.toRingHom

@[simp] theorem seriesEquiv_constant (c : E) :
    seriesEquiv a (PowerSeries.C c) = PowerSeries.C (a c) :=
  PowerSeries.map_C a.toRingHom c

/-- Fraction-field transport extends the genuine series ring equivalence. -/
def fractionEquiv : TraitFraction E ≃+* TraitFraction F :=
  IsFractionRing.ringEquivOfRingEquiv (K := TraitFraction E) (L := TraitFraction F)
    (seriesEquiv a)

@[simp] theorem fractionEquiv_overSeries (f : PowerSeries E) :
    fractionEquiv a (algebraMap (PowerSeries E) (TraitFraction E) f) =
      algebraMap (PowerSeries F) (TraitFraction F) (seriesEquiv a f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (seriesEquiv a) f

/-- A chosen extension of a genuine fraction-field equivalence. -/
def closureEquiv : TraitClosure E ≃+* TraitClosure F :=
  IsAlgClosure.equivOfEquiv (TraitClosure E) (TraitClosure F) (fractionEquiv a)

@[simp] theorem closureEquiv_overFraction (x : TraitFraction E) :
    closureEquiv a (algebraMap (TraitFraction E) (TraitClosure E) x) =
      algebraMap (TraitFraction F) (TraitClosure F) (fractionEquiv a x) :=
  IsAlgClosure.equivOfEquiv_algebraMap (TraitClosure E) (TraitClosure F)
    (fractionEquiv a) x

@[simp] theorem closureEquiv_symm_overFraction (x : TraitFraction F) :
    (closureEquiv a).symm (algebraMap (TraitFraction F) (TraitClosure F) x) =
      algebraMap (TraitFraction E) (TraitClosure E) ((fractionEquiv a).symm x) :=
  IsAlgClosure.equivOfEquiv_symm_algebraMap (TraitClosure E) (TraitClosure F)
    (fractionEquiv a) x

/-- The explicit SAME-base algebra square for this chosen closure extension. -/
theorem closureEquiv_comp_algebraMap :
    (closureEquiv a).toRingHom.comp (algebraMap (TraitFraction E) (TraitClosure E)) =
      (algebraMap (TraitFraction F) (TraitClosure F)).comp (fractionEquiv a).toRingHom :=
  IsAlgClosure.equivOfEquiv_comp_algebraMap (TraitClosure E) (TraitClosure F)
    (fractionEquiv a)

/-- Every embedded series is transported by literal coefficient transport. -/
@[simp] theorem closureEquiv_overEverySeries (f : PowerSeries E) :
    closureEquiv a (seriesEmbedding f) = seriesEmbedding (seriesEquiv a f) := by
  change closureEquiv a
    (algebraMap (TraitFraction E) (TraitClosure E)
      (algebraMap (PowerSeries E) (TraitFraction E) f)) = _
  rw [closureEquiv_overFraction, fractionEquiv_overSeries]
  rfl

@[simp] theorem closureEquiv_parameter :
    closureEquiv a (seriesEmbedding (PowerSeries.X : PowerSeries E)) =
      seriesEmbedding (PowerSeries.X : PowerSeries F) := by
  rw [closureEquiv_overEverySeries, seriesEquiv_parameter]

@[simp] theorem closureEquiv_constant (c : E) :
    closureEquiv a (seriesEmbedding (PowerSeries.C c)) =
      seriesEmbedding (PowerSeries.C (a c)) := by
  rw [closureEquiv_overEverySeries, seriesEquiv_constant]

/-- Conjugation fixes the target fraction field, not merely its constants. -/
def forward (r : TraitGroup E) : TraitGroup F :=
  AlgEquiv.ofRingEquiv
    (f := (closureEquiv a).symm.trans (r.toRingEquiv.trans (closureEquiv a))) (by
      intro x
      change closureEquiv a (r ((closureEquiv a).symm
        (algebraMap (TraitFraction F) (TraitClosure F) x))) = _
      rw [closureEquiv_symm_overFraction, r.commutes, closureEquiv_overFraction,
        RingEquiv.apply_symm_apply])

@[simp] theorem forward_apply (r : TraitGroup E) (x : TraitClosure F) :
    forward a r x = closureEquiv a (r ((closureEquiv a).symm x)) := rfl

/-- The inverse uses the SAME closure extension's inverse. -/
def backward (r : TraitGroup F) : TraitGroup E :=
  AlgEquiv.ofRingEquiv
    (f := (closureEquiv a).trans (r.toRingEquiv.trans (closureEquiv a).symm)) (by
      intro x
      change (closureEquiv a).symm (r (closureEquiv a
        (algebraMap (TraitFraction E) (TraitClosure E) x))) = _
      rw [closureEquiv_overFraction, r.commutes, closureEquiv_symm_overFraction,
        RingEquiv.symm_apply_apply])

@[simp] theorem backward_apply (r : TraitGroup F) (x : TraitClosure E) :
    backward a r x = (closureEquiv a).symm (r (closureEquiv a x)) := rfl

/-- A genuine equivalence of the actual base-field automorphism groups. -/
def groupEquiv : TraitGroup E ≃* TraitGroup F where
  toFun := forward a
  invFun := backward a
  left_inv := by
    intro r
    ext x
    simp only [backward_apply, forward_apply, RingEquiv.symm_apply_apply]
  right_inv := by
    intro r
    ext x
    simp only [forward_apply, backward_apply, RingEquiv.apply_symm_apply]
  map_mul' := by
    intro r s
    ext x
    simp only [forward_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]

@[simp] theorem groupEquiv_apply (r : TraitGroup E) (x : TraitClosure F) :
    groupEquiv a r x = closureEquiv a (r ((closureEquiv a).symm x)) := rfl

@[simp] theorem groupEquiv_symm_apply (r : TraitGroup F) (x : TraitClosure E) :
    (groupEquiv a).symm r x = (closureEquiv a).symm (r (closureEquiv a x)) := rfl

/-- The actual group action intertwines on every closure element. -/
theorem groupEquiv_intertwines (r : TraitGroup E) (x : TraitClosure E) :
    groupEquiv a r (closureEquiv a x) = closureEquiv a (r x) := by
  rw [groupEquiv_apply, RingEquiv.symm_apply_apply]

/-- Explicit fixed-base compatibility of the computed target group element. -/
theorem groupEquiv_commutes (r : TraitGroup E) (x : TraitFraction F) :
    groupEquiv a r (algebraMap (TraitFraction F) (TraitClosure F) x) =
      algebraMap (TraitFraction F) (TraitClosure F) x :=
  (groupEquiv a r).commutes x

/-- Every series square intertwines the two actual inertia actions. -/
theorem groupEquiv_overEverySeries (r : TraitGroup E) (f : PowerSeries E) :
    groupEquiv a r (seriesEmbedding (seriesEquiv a f)) =
      closureEquiv a (r (seriesEmbedding f)) := by
  rw [← closureEquiv_overEverySeries, groupEquiv_intertwines]

end PrimeGap182.TypeIII.ActualTraitGroupFromCoefficientRingEquiv
