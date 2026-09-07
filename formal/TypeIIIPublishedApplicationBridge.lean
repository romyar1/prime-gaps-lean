import TypeIIIPublishedTypeIII
import TypeIIIPublishedCovarianceRules
import TypeIIIPublishedPhaseApplication
import TypeIIICoreTraceCoordinates

/-!
# Supplying the Type III application from traces and local representations

This bridge derives the profile, phase-containment and coefficient-covariance
fields of `PublishedTypeIII.Application`. Its input contains no Fourier
estimate, no exclusion of transformed supports, and no phase list for the
finished correlation core. Fu's general cubic rule and the actual supplied
finite-origin/Mackey maps give that phase list; the all-extension finite-sum
identity and generic Chebotarev/Fourier rules give covariance.

All-extension traces and prime-field spectra now refer to the same typed
Weil lift of each physical object. Geometric constituents themselves need
no arithmetic lift. The remaining realization data are explicit. In particular, the supplied
inertia representations and maps must be those of the physical objects, and
the physical construction must have the specified traces, purity and uniform
complexity. This file does not manufacture an instance of the geometric
theory or disguise those identifications as a published theorem.
-/

noncomputable section
open scoped Classical

namespace PrimeGap182.TypeIII.PublishedApplicationBridge

open PublishedSupportRules PublishedFourierRules PublishedStalkCertificate
open PublishedTypeIII PublishedCovarianceRules PublishedPhaseApplication

universe u v w z

/-- The two conjugated corners in the original four-cycle. -/
def conjugatedCorner (e : PhaseRectangle) : Bool := decide (e.1 ≠ e.2)

theorem conjugatedCorner_cycleRectangle (i : Fin 4) :
    conjugatedCorner (cycleRectangle i) = ![false, true, false, true] i := by
  fin_cases i <;> decide

theorem prime_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

variable {p : ℕ} [Fact p.Prime] {theory : Theory.{u, v} p}
  {E : Type w} [Field E] [CharZero E] {G : Type z} [Group G]

/-- Compatibility of the geometric radial observables with actual finite
dimensional representations. Inertia is at t=0 after t=T², with characters
AS(beta/T). This is realization data for the generic imported rules. -/
structure RadialRealization (theory : Theory.{u, v} p)
    (D : PhaseData (AlgebraicClosure (ZMod p)) E G) where
  inertia : theory.Obj → FDRep E G
  profile : ∀ P, theory.fourier.HasSimpleRadialPhases P ↔ D.HasProfile (inertia P)
  phases : ∀ P, theory.fourier.phases P = D.phases (inertia P)

variable {B Rphys : ℕ} {α m m' n n' : ZMod p}
  {D : PhaseData (AlgebraicClosure (ZMod p)) E G}
  {C : CubicFourierData (AlgebraicClosure (ZMod p)) E G}

/-- Local application data before the phase calculation. The exact
finite-origin maps and the Mackey comparison are in `CoreLocalData`.
No profile, phase containment or noncancellation conclusion is a field. -/
structure LocalFamilyData (radial : RadialRealization theory D)
    (family : FamilyConstruction B Rphys p α m m' n n' theory.data theory.qst
      theory.realization theory.fourier.fourier theory.traceWeights)
    (C : CubicFourierData (AlgebraicClosure (ZMod p)) E G) where
  cores : PhaseRectangle → FDRep E G
  localData : ∀ e : PhaseRectangle,
    CoreLocalData C (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) α)
      (residuePair p m m' e.1) (residuePair p n n' e.2) (cores e)
  tensor_comparison : ∀ S ∈ nonemptyCoreSubsets,
    IsSubquotient (radial.inertia (family.physicalObjects S))
      (selectedTensor (rectangleSubset S)
        (fun e => signedRepresentation (conjugatedCorner e) (cores e)))

/-- The local Fourier calculation populates both radial fields used by
the final support theorem. Distinctness is unnecessary for this containment;
it is used later for the proved scalar noncancellation. -/
theorem local_family_profile
    (radial : RadialRealization theory D)
    (family : FamilyConstruction B Rphys p α m m' n n' theory.data theory.qst
      theory.realization theory.fourier.fourier theory.traceWeights)
    (data : LocalFamilyData radial family C) (R : PhaseRules D) (F : FuRules p D C)
    (hp : 3 < p) (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) :
    theory.fourier.HasSimpleRadialPhases (family.physicalObjects S) ∧
      theory.fourier.phases (family.physicalObjects S) ⊆
        rectangleAllowedPhases (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) α)
          (residuePair p m m') (residuePair p n n') (rectangleSubset S) := by
  have h := subquotient_rectangle_profile R F hp (geometric_two_ne_zero p hp)
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) α) (residue_ne_zero p α hα)
    (residuePair p m m') (residuePair p n n') (residuePair_ne_zero p m m' hm hm')
    (rectangleSubset S) data.cores conjugatedCorner (fun e _ => data.localData e)
    (radial.inertia (family.physicalObjects S)) (data.tensor_comparison S hS)
  refine ⟨(radial.profile _).mpr h.1, ?_⟩
  rw [radial.phases]
  exact h.2

/-- The separate uniform quantitative-sheaf applications. These are
bounds on the stated published functions at the actual objects, with no
assumed monotonicity of those functions. -/
structure TransformedBounds (Dcore Nproper Npunct : ℕ)
    (family : FamilyConstruction B Rphys p α m m' n n' theory.data theory.qst
      theory.realization theory.fourier.fourier theory.traceWeights) : Prop where
  finite : ∀ S ∈ nonemptyCoreSubsets,
    theory.qst.ordinarySupportBound
      (theory.data.complexity (theory.fourier.fourier (family.physicalObjects S))) ≤ Dcore
  curve : ∀ S ∈ nonemptyCoreSubsets,
    theory.degrees.degreeBound
      (theory.data.complexity (theory.fourier.fourier (family.physicalObjects S))) ≤ Dcore
  proper : ∀ S ∈ nonemptyCoreSubsets,
    theory.qst.properDegreeBound
      (theory.data.complexity (theory.fourier.fourier (family.physicalObjects S))) ≤ Nproper
  punctual : ∀ S ∈ nonemptyCoreSubsets,
    theory.qst.constituentBound
      (theory.data.complexity (theory.fourier.fourier (family.physicalObjects S))) ≤ Npunct

/-- The final Type III application from the actual trace and local-map
inputs. Covariance and the finished phase list are derived here, and then
`Application.finiteFourierBound` / `curveFourierBound` give the unchanged
estimates. The uniform version uses these applications at the fixed cutoff. -/
def applicationOfTraceAndLocalData
    (Dcore Nproper Npunct : ℕ) (hp : 3 < p)
    (family : FamilyConstruction B Rphys p α m m' n n' theory.data theory.qst
      theory.realization theory.fourier.fourier theory.traceWeights)
    (radial : RadialRealization theory D) (data : LocalFamilyData radial family C)
    (R : PhaseRules D) (F : FuRules p D C)
    (traceData : TraceData p theory.realization) (sigma : ℂ ≃+* ℂ)
    (hsigma : ∀ t : ZMod p, sigma (ZMod.stdAddChar t) = ZMod.stdAddChar (2 * t))
    (chebotarev : ChebotarevRules (T := theory.coefficient) traceData sigma)
    (fourierCovariance : FourierCovarianceRules
      (T := theory.coefficient) (F := theory.fourier)
      (Units.mk0 2 (prime_two_ne_zero p hp)))
    (htorus : ∀ S ∈ nonemptyCoreSubsets, traceData.TorusIC (family.physicalObjects S))
    (htrace : ∀ S ∈ nonemptyCoreSubsets,
      ExpectedCoreTrace traceData (family.physicalLift S) α m m' n n' S)
    (bounds : TransformedBounds Dcore Nproper Npunct family)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    Application B Rphys Dcore Nproper Npunct p α m m' n n' theory where
  construction := family
  eight := geometricUnit p ((Units.mk0 2 (prime_two_ne_zero p hp)) ^ 3)
  eight_value := geometricUnit_two_cube (prime_two_ne_zero p hp)
  profile := fun _ S hS => (local_family_profile radial family data R F hp hα hm hm' S hS).1
  phases := fun _ S hS => (local_family_profile radial family data R F hp hα hm hm' S hS).2
  covariance := fun S hS => fourier_covariance_of_physical _ fourierCovariance
    (family.physicalObjects S)
    (physical_covariance_of_expected_trace traceData sigma chebotarev
      (family.physicalObjects S) (family.physicalLift S) (htorus S hS)
      (Units.mk0 2 (prime_two_ne_zero p hp))
      hsigma α m m' n n' S hm hm' hn hn' (htrace S hS))
  finite_support_bound := bounds.finite
  curve_degree_bound := bounds.curve
  proper_degree_bound := bounds.proper
  punctual_bound := bounds.punctual

end PrimeGap182.TypeIII.PublishedApplicationBridge

#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.conjugatedCorner
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.conjugatedCorner_cycleRectangle
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.prime_two_ne_zero
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.RadialRealization
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.RadialRealization.mk
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.RadialRealization.inertia
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.RadialRealization.profile
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.RadialRealization.phases
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.LocalFamilyData
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.LocalFamilyData.mk
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.LocalFamilyData.cores
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.LocalFamilyData.localData
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.LocalFamilyData.tensor_comparison
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.local_family_profile
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.TransformedBounds
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.TransformedBounds.mk
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.TransformedBounds.finite
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.TransformedBounds.curve
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.TransformedBounds.proper
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.TransformedBounds.punctual
#print axioms PrimeGap182.TypeIII.PublishedApplicationBridge.applicationOfTraceAndLocalData
