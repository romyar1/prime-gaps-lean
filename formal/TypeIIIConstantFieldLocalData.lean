import TypeIIIPhaseFieldConstants

/-!
# Transport the local application across an algebraic constant extension

Reparametrize the cubic outputs and phase values by the constructed
phase-field isomorphism. The actual finite-dimensional representations,
finite-origin maps, exactness, tameness and rank are unchanged. The
transport includes the general phase laws and Fu's scalar equation;
it does not supply a new family or assume its comparison.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical

namespace PrimeGap182.TypeIII.ConstantFieldLocalData

open PublishedPhaseApplication PhaseFieldConstants

universe u v w z
variable (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type w} [Field E] {G : Type z} [Group G]

/-- Reparametrize the same cubic Fourier representations. -/
def cubicData (C : CubicFourierData K E G) : CubicFourierData L E G where
  output a q := C.output ((phaseFieldEquiv K L).symm a) ((phaseFieldEquiv K L).symm q)

/-- Retain the profiles and transport only their phase coordinates. -/
def phaseData (D : PhaseData K E G) : PhaseData L E G where
  HasProfile := D.HasProfile
  phases A := phaseFieldEquiv K L '' D.phases A

/-- All local-family data retain the same representation and exact
sequence maps. Only the three cubic roots are transported. -/
def coreLocalData (C : CubicFourierData K E G) (alpha m n : K) (H : FDRep E G)
    (d : CoreLocalData C alpha m n H) :
    CoreLocalData (cubicData K L C) (algebraMap K L alpha)
      (algebraMap K L m) (algebraMap K L n) H where
  q i := phaseFieldEquiv K L (d.q i)
  q_cube i := by
    have h := congrArg (phaseFieldEquiv K L) (d.q_cube i)
    simpa only [map_pow, map_div₀, phaseFieldEquiv_constant, phaseFieldEquiv_direction] using h
  V := d.V
  T := d.T
  mackeyFourierComparison := by
    have hscale : (phaseFieldEquiv K L).symm
        (radialScale (algebraMap K L alpha) (algebraMap K L m)) = radialScale alpha m := by
      rw [← phaseFieldEquiv_radialScale K L, RingEquiv.symm_apply_apply]
    change Representation.Equiv d.V.ρ
      (finiteSum (fun i => C.output
        ((phaseFieldEquiv K L).symm (radialScale (algebraMap K L alpha) (algebraMap K L m)))
        ((phaseFieldEquiv K L).symm (phaseFieldEquiv K L (d.q i))))).ρ
    rw [hscale]
    have hout : (fun i : Fin 3 => C.output (radialScale alpha m)
        ((phaseFieldEquiv K L).symm (phaseFieldEquiv K L (d.q i)))) =
        (fun i : Fin 3 => C.output (radialScale alpha m) (d.q i)) := by
      funext i
      rw [RingEquiv.symm_apply_apply]
    rw [hout]
    exact d.mackeyFourierComparison
  toVanishing := d.toVanishing
  toTame := d.toTame
  exact := d.exact
  tame := d.tame
  core_rank := d.core_rank

variable [CharZero E]

/-- The general phase laws survive the coordinate change. In particular,
addition and negation of phases still match tensor products and duals. -/
theorem phaseRules (D : PhaseData K E G) (R : PhaseRules D) : PhaseRules (phaseData K L D) where
  transport A B f hf := by
    obtain ⟨hp, he⟩ := R.transport A B f hf
    exact ⟨hp, congrArg (fun s => phaseFieldEquiv K L '' s) he⟩
  sum_profile V hV := R.sum_profile V hV
  sum_phases V hV := by
    rintro beta ⟨b, hb, rfl⟩
    obtain ⟨i, hi⟩ := R.sum_phases V hV b hb
    exact ⟨i, b, hi, rfl⟩
  tensor_profile s V hV := R.tensor_profile s V hV
  tensor_phases s V hV := by
    rintro beta ⟨b, hb, rfl⟩
    obtain ⟨bs, hbs, he⟩ := R.tensor_phases s V hV b hb
    refine ⟨fun i => phaseFieldEquiv K L (bs i), fun i hi => ⟨bs i, hbs i hi, rfl⟩, ?_⟩
    rw [he, map_sum]
  dual_profile V hV := R.dual_profile V hV
  dual_phases V hV := by
    rintro beta ⟨b, hb, rfl⟩
    exact ⟨-b, R.dual_phases V hV b hb, map_neg (phaseFieldEquiv K L) b⟩
  subquotient_profile A B h hB := R.subquotient_profile A B h hB
  subquotient_phases A B h hB := Set.image_mono (R.subquotient_phases A B h hB)
  map_to_trivial_zero A B hA hzero hB f :=
    R.map_to_trivial_zero A B hA (fun hz => hzero ⟨0, hz, map_zero (phaseFieldEquiv K L)⟩) hB f

/-- Fu's exact cubic scalar equation is preserved; neither a new
Fourier estimate nor a family phase conclusion is assumed. -/
theorem fuRules (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (D : PhaseData K E G) (C : CubicFourierData K E G) (F : FuRules p D C) :
    FuRules p (phaseData K L D) (cubicData K L C) where
  formula hp a q ha hq := by
    have ha' : (phaseFieldEquiv K L).symm a ≠ 0 := by
      intro h
      apply ha
      simpa only [RingEquiv.apply_symm_apply, map_zero] using congrArg (phaseFieldEquiv K L) h
    have hq' : (phaseFieldEquiv K L).symm q ≠ 1 := by
      intro h
      apply hq
      simpa only [RingEquiv.apply_symm_apply, map_one] using congrArg (phaseFieldEquiv K L) h
    obtain ⟨hp', hr, hb⟩ := F.formula hp _ _ ha' hq'
    refine ⟨hp', hr, ?_⟩
    rintro beta ⟨b, hb', rfl⟩
    have h := congrArg (phaseFieldEquiv K L) (hb b hb')
    simpa only [map_pow, map_mul, map_ofNat, map_sub, map_one, RingEquiv.apply_symm_apply] using h

/-- This is the constant-field type required by the posted bridge,
with the ORIGINAL representation and original finite-origin maps. -/
def algebraicClosureCoreLocalData (C : CubicFourierData K E G)
    (alpha m n : K) (H : FDRep E G) (d : CoreLocalData C alpha m n H) :
    CoreLocalData (cubicData K (AlgebraicClosure K) C)
      (algebraMap K (AlgebraicClosure K) alpha)
      (algebraMap K (AlgebraicClosure K) m)
      (algebraMap K (AlgebraicClosure K) n) H :=
  coreLocalData K (AlgebraicClosure K) C alpha m n H d

end PrimeGap182.TypeIII.ConstantFieldLocalData

#print axioms PrimeGap182.TypeIII.ConstantFieldLocalData.cubicData
#print axioms PrimeGap182.TypeIII.ConstantFieldLocalData.phaseData
#print axioms PrimeGap182.TypeIII.ConstantFieldLocalData.coreLocalData
#print axioms PrimeGap182.TypeIII.ConstantFieldLocalData.phaseRules
#print axioms PrimeGap182.TypeIII.ConstantFieldLocalData.fuRules
#print axioms PrimeGap182.TypeIII.ConstantFieldLocalData.algebraicClosureCoreLocalData
