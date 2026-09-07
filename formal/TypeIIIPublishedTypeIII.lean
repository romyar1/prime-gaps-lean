import TypeIIIPublishedStalkCertificate
import TypeIIIPublishedFourierRules

/-!
# The original Type III input conditional on explicit published rules

`Theory` bundles the generic BBD, quantitative-sheaf, Fourier, local-inertia,
coefficient-transport, trace and weight laws. `Application` is separate
actual-family data: the physical construction, radial profile and phase
containment, coefficient/eight covariance, and numerical complexity bounds.
It contains neither full support of transformed constituents nor a Fourier
norm estimate. Those conclusions are derived below.

The four original factors are identified with the rectangle in the actual
cyclic order `(0,0),(1,0),(1,1),(0,1)`. All prime-field parameter inclusions,
nonvanishing and distinctness deductions are proved. The finite and curve
adapters return the original support records for the original common
certificate with physical boundary constant one.

The final uniform package fixes `B,Rphys,Dcore,Nproper,Npunct` before the
prime and all five residue parameters. Its cutoff is
`max 3 (8^(max Nproper Npunct))`. The endpoint is the unchanged
`LocalFourierHypothesis`, then `HasFiniteExceptionalTypeIIIInput`.
This remains conditional on the stated generic laws and actual-family
construction/application obligations; it does not instantiate the unfinished
foundational adic construction or assert those family obligations by fiat.
-/

noncomputable section
open scoped Classical

namespace PrimeGap182.TypeIII.PublishedTypeIII

open PublishedSupportRules PublishedFourierRules PublishedStalkCertificate

universe u v

/-- The actual cyclic order of the four factors in the arithmetic cycle. -/
def cycleRectangle : Fin 4 ≃ PhaseRectangle where
  toFun := ![(0, 0), (1, 0), (1, 1), (0, 1)]
  invFun e := if e.1 = 0 then (if e.2 = 0 then 0 else 3)
    else if e.2 = 0 then 1 else 2
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> decide

@[simp] theorem cycleRectangle_zero : cycleRectangle 0 = (0, 0) := rfl
@[simp] theorem cycleRectangle_one : cycleRectangle 1 = (1, 0) := rfl
@[simp] theorem cycleRectangle_two : cycleRectangle 2 = (1, 1) := rfl
@[simp] theorem cycleRectangle_three : cycleRectangle 3 = (0, 1) := rfl

def rectangleSubset (S : Finset (Fin 4)) : Finset PhaseRectangle :=
  S.image cycleRectangle

theorem rectangleSubset_nonempty (S : Finset (Fin 4))
    (hS : S ∈ nonemptyCoreSubsets) : (rectangleSubset S).Nonempty :=
  (Finset.nonempty_iff_ne_empty.mpr ((mem_nonemptyCoreSubsets S).mp hS)).image
    cycleRectangle

@[simp] theorem rectangleSubset_card (S : Finset (Fin 4)) :
    (rectangleSubset S).card = S.card :=
  Finset.card_image_of_injective S cycleRectangle.injective

/-- The actual row or column parameter pair in the algebraic closure. -/
def residuePair (p : ℕ) [Fact p.Prime] (a b : ZMod p) :
    Fin 2 → AlgebraicClosure (ZMod p) :=
  ![algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a,
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) b]

theorem residue_ne_zero (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a ≠ 0 := by
  intro h
  exact ha ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
    (by simpa only [map_zero] using h))

theorem residuePair_ne_zero (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 2) : residuePair p a b i ≠ 0 := by
  fin_cases i
  · exact residue_ne_zero p a ha
  · exact residue_ne_zero p b hb

theorem residuePair_injective (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hab : a ≠ b) : Function.Injective (residuePair p a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hab ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective hij)).elim
  · exact (hab ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective hij.symm)).elim
  · rfl

/-- A fixed cutoff large enough for both geometric support arguments. -/
def cutoff (Nproper Npunct : ℕ) : ℕ := max 3 (8 ^ max Nproper Npunct)

theorem proper_power_le_cutoff (Nproper Npunct : ℕ) :
    8 ^ Nproper ≤ cutoff Nproper Npunct :=
  (Nat.pow_le_pow_right (by decide : 0 < 8) (le_max_left _ _)).trans (le_max_right _ _)

theorem punctual_power_le_cutoff (Nproper Npunct : ℕ) :
    8 ^ Npunct ≤ cutoff Nproper Npunct :=
  (Nat.pow_le_pow_right (by decide : 0 < 8) (le_max_right _ _)).trans (le_max_right _ _)

theorem three_lt_of_cutoff {Nproper Npunct p : ℕ}
    (hp : cutoff Nproper Npunct < p) : 3 < p :=
  (le_max_left _ _).trans_lt hp

theorem geometric_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (2 : AlgebraicClosure (ZMod p)) ≠ 0 := by
  intro h
  have hdiv := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p 2).mp h
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

/-- Only generic published-theory observables and laws. The object and
curve-object types may vary with the prime in a uniform application. -/
structure Theory (p : ℕ) [Fact p.Prime] where
  Obj : Type u
  CurveObj : Type v
  data : SurfaceData (AlgebraicClosure (ZMod p)) Obj
  bbd : BBDRules data
  qst : QSTRules data
  classification : SupportClassification data
  degrees : OrdinarySupportDegreeRules data
  coefficient : CoefficientTransport data
  fourier : FourierData (AlgebraicClosure (ZMod p)) Obj CurveObj
  localRules : LocalRules data coefficient fourier
  realization : RationalStalkRealization p data
  traceWeights : TraceWeightRules p data realization fourier.fourier

/-- Family-specific obligations. The profile and phase containment are
needed only in the distinct-index branch. A chosen unit of value eight
allows the separately proved arithmetic/sheaf covariance constructions to
be used without changing their representatives. -/
structure Application (B Rphys Dcore Nproper Npunct : ℕ) (p : ℕ) [Fact p.Prime]
    (α m m' n n' : ZMod p) (theory : Theory.{u, v} p) where
  construction : FamilyConstruction B Rphys p α m m' n n' theory.data theory.qst
    theory.realization theory.fourier.fourier theory.traceWeights
  eight : (AlgebraicClosure (ZMod p))ˣ
  eight_value : (eight : AlgebraicClosure (ZMod p)) = 8
  profile : (m ≠ m' ∧ n ≠ n') → ∀ S ∈ nonemptyCoreSubsets,
    theory.fourier.HasSimpleRadialPhases (construction.physicalObjects S)
  phases : (m ≠ m' ∧ n ≠ n') → ∀ S ∈ nonemptyCoreSubsets,
    theory.fourier.phases (construction.physicalObjects S) ⊆
      rectangleAllowedPhases (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) α)
        (residuePair p m m') (residuePair p n n') (rectangleSubset S)
  covariance : ∀ S ∈ nonemptyCoreSubsets,
    theory.coefficient.Isomorphic
      (theory.coefficient.coefficient (theory.fourier.fourier (construction.physicalObjects S)))
      (theory.coefficient.dilate eight (theory.fourier.fourier (construction.physicalObjects S)))
  finite_support_bound : ∀ S ∈ nonemptyCoreSubsets,
    theory.qst.ordinarySupportBound
      (theory.data.complexity (theory.fourier.fourier (construction.physicalObjects S))) ≤ Dcore
  curve_degree_bound : ∀ S ∈ nonemptyCoreSubsets,
    theory.degrees.degreeBound
      (theory.data.complexity (theory.fourier.fourier (construction.physicalObjects S))) ≤ Dcore
  proper_degree_bound : ∀ S ∈ nonemptyCoreSubsets,
    theory.qst.properDegreeBound
      (theory.data.complexity (theory.fourier.fourier (construction.physicalObjects S))) ≤ Nproper
  punctual_bound : ∀ S ∈ nonemptyCoreSubsets,
    theory.qst.constituentBound
      (theory.data.complexity (theory.fourier.fourier (construction.physicalObjects S))) ≤ Npunct

namespace Application

variable {B Rphys Dcore Nproper Npunct p : ℕ} [Fact p.Prime]
    {α m m' n n' : ZMod p} {theory : Theory.{u, v} p}
    (app : Application B Rphys Dcore Nproper Npunct p α m m' n n' theory)

/-- The common certificate already constructed from the physical inputs. -/
def certificate : TypeIIIStalkCertificate p B 1 Rphys α m m' n n' :=
  app.construction.certificate theory.bbd

@[simp] theorem certificate_transformed (S : Finset (Fin 4)) (h k : ZMod p) :
    app.certificate.transformed S h k =
      theory.realization.stalk
        (theory.traceWeights.fourierLift (app.construction.physicalLift S))
        h k := rfl

/-- Transformed full support is a theorem from the generic local Fourier
rules, the proved rectangle obstruction and the supplied family profile
and covariance. It is not a field of `Application`. -/
theorem transformed_full_constituents (hp : cutoff Nproper Npunct < p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hdistinct : m ≠ m' ∧ n ≠ n') (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) :
    theory.data.NoProperConstituents
      (theory.fourier.fourier (app.construction.physicalObjects S)) := by
  apply no_proper_constituents_of_rectangle_phases theory.bbd theory.qst theory.classification
    theory.localRules (app.construction.physicalObjects S)
    (app.construction.full_constituents S hS) (app.profile hdistinct S hS)
    (geometric_two_ne_zero p (three_lt_of_cutoff hp)) _ (residue_ne_zero p α hα)
    (residuePair p m m') (residuePair p n n')
    (residuePair_ne_zero p m m' hm hm') (residuePair_ne_zero p n n' hn hn')
    (residuePair_injective p m m' hdistinct.1) (residuePair_injective p n n' hdistinct.2)
    (rectangleSubset S) (rectangleSubset_nonempty S hS) (app.phases hdistinct S hS)
    app.eight app.eight_value (app.covariance S hS)
  exact (Nat.pow_le_pow_right (by decide : 0 < 8) (app.proper_degree_bound S hS)).trans_lt
    ((proper_power_le_cutoff Nproper Npunct).trans_lt hp)

/-- The original finite-support certificate for the literal transformed
spectra, with the common uniform bound `Dcore`. -/
def finiteSupport (hp : cutoff Nproper Npunct < p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hdistinct : m ≠ m' ∧ n ≠ n') : TypeIIIFiniteStalkSupport app.certificate Dcore :=
  PublishedStalkSupport.finiteSupport app.certificate theory.data theory.bbd theory.qst
    theory.realization (fun S => theory.fourier.fourier (app.construction.physicalObjects S))
    (fun S => theory.traceWeights.fourierLift (app.construction.physicalLift S))
    (fun S _ h k => app.certificate_transformed S h k)
    (fun S hS => app.construction.transformed_pure S hS)
    (app.transformed_full_constituents hp hα hm hm' hn hn' hdistinct)
    app.finite_support_bound

/-- The original curve-support certificate. This support conclusion also
holds in the distinct-index case, but the stronger finite one is used there. -/
def curveSupport (hp : cutoff Nproper Npunct < p) :
    TypeIIICurveStalkSupport app.certificate Dcore :=
  PublishedStalkSupport.curveSupport app.certificate theory.data theory.bbd theory.qst
    theory.degrees theory.coefficient theory.realization
    (fun S => theory.fourier.fourier (app.construction.physicalObjects S))
    (fun S => theory.traceWeights.fourierLift (app.construction.physicalLift S))
    app.eight app.eight_value Npunct (cutoff Nproper Npunct)
    (punctual_power_le_cutoff Nproper Npunct) hp
    (fun S _ h k => app.certificate_transformed S h k)
    (fun S hS => app.construction.transformed_pure S hS)
    app.covariance app.curve_degree_bound app.punctual_bound

include app in
theorem finiteFourierBound (hbase : BaselineLocalInputs)
    (hp : cutoff Nproper Npunct < p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hdistinct : m ≠ m' ∧ n ≠ n') :
    FiniteExceptionalFourierBound p (uniformStalkConstant B 1 Rphys)
      (15 * Dcore) α m m' n n' :=
  (app.finiteSupport hp hα hm hm' hn hn' hdistinct).fourierBound hbase hα hm hm' hn hn'

include app in
theorem curveFourierBound (hbase : BaselineLocalInputs)
    (hp : cutoff Nproper Npunct < p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    CurveExceptionalFourierBound p (uniformStalkConstant B 1 Rphys)
      (15 * Dcore) α m m' n n' :=
  (app.curveSupport hp).fourierBound hbase hα hm hm' hn hn'

end Application

/-- Uniformity is asserted before choosing any prime or residue parameter.
The fields contain generic theory and actual-family application data,
without an assumed local Fourier inequality or transformed exclusion. -/
structure UniformApplications (B Rphys Dcore Nproper Npunct : ℕ) where
  theory : ∀ (p : ℕ) [Fact p.Prime], cutoff Nproper Npunct < p → Theory.{u, v} p
  application : ∀ (p : ℕ) [Fact p.Prime] (hp : cutoff Nproper Npunct < p)
    (α m m' n n' : ZMod p),
    α ≠ 0 → m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
      Application B Rphys Dcore Nproper Npunct p α m m' n n' (theory p hp)

namespace UniformApplications

variable {B Rphys Dcore Nproper Npunct : ℕ}
    (apps : UniformApplications.{u, v} B Rphys Dcore Nproper Npunct)

/-- The existing uniform certificate interface is populated by the proved
support adapters; none of its support fields remains an input here. -/
def stalkCertificates :
    UniformTypeIIIStalkCertificates B 1 Rphys Dcore (cutoff Nproper Npunct) where
  common := fun p _ hp α m m' n n' hα hm hm' hn hn' =>
    (apps.application p hp α m m' n n' hα hm hm' hn hn').certificate
  finite := fun p _ hp α m m' n n' hα hm hm' hn hn' hdistinct =>
    (apps.application p hp α m m' n n' hα hm hm' hn hn').finiteSupport
      hp hα hm hm' hn hn' hdistinct
  curve := fun p _ hp α m m' n n' hα hm hm' hn hn' _ =>
    (apps.application p hp α m m' n n' hα hm hm' hn hn').curveSupport hp

include apps in
/-- The exact original Type III local Fourier proposition follows from
the displayed generic laws and uniform actual-family inputs. -/
theorem localFourierHypothesis (hbase : BaselineLocalInputs) :
    LocalFourierHypothesis (uniformStalkConstant B 1 Rphys) (15 * Dcore)
      (cutoff Nproper Npunct) :=
  localFourierHypothesis_of_uniform_stalk_certificates hbase B 1 Rphys Dcore
    (cutoff Nproper Npunct) apps.stalkCertificates

include apps in
theorem hasFiniteExceptionalTypeIIIInput (hbase : BaselineLocalInputs) :
    HasFiniteExceptionalTypeIIIInput :=
  hasFiniteExceptionalTypeIIIInput_of_uniform_stalk_certificates hbase B 1 Rphys Dcore
    (cutoff Nproper Npunct) apps.stalkCertificates

end UniformApplications

#print axioms cycleRectangle
#print axioms cycleRectangle_zero
#print axioms cycleRectangle_one
#print axioms cycleRectangle_two
#print axioms cycleRectangle_three
#print axioms rectangleSubset
#print axioms rectangleSubset_nonempty
#print axioms rectangleSubset_card
#print axioms residuePair
#print axioms residue_ne_zero
#print axioms residuePair_ne_zero
#print axioms residuePair_injective
#print axioms cutoff
#print axioms proper_power_le_cutoff
#print axioms punctual_power_le_cutoff
#print axioms three_lt_of_cutoff
#print axioms geometric_two_ne_zero
#print axioms Theory
#print axioms Theory.mk
#print axioms Theory.rec
#print axioms Theory.recOn
#print axioms Theory.casesOn
#print axioms Theory.noConfusionType
#print axioms Theory.noConfusion
#print axioms Theory.Obj
#print axioms Theory.CurveObj
#print axioms Theory.data
#print axioms Theory.bbd
#print axioms Theory.qst
#print axioms Theory.classification
#print axioms Theory.degrees
#print axioms Theory.coefficient
#print axioms Theory.fourier
#print axioms Theory.localRules
#print axioms Theory.realization
#print axioms Theory.traceWeights
#print axioms Application
#print axioms Application.mk
#print axioms Application.rec
#print axioms Application.recOn
#print axioms Application.casesOn
#print axioms Application.noConfusionType
#print axioms Application.noConfusion
#print axioms Application.construction
#print axioms Application.eight
#print axioms Application.eight_value
#print axioms Application.profile
#print axioms Application.phases
#print axioms Application.covariance
#print axioms Application.finite_support_bound
#print axioms Application.curve_degree_bound
#print axioms Application.proper_degree_bound
#print axioms Application.punctual_bound
#print axioms Application.certificate
#print axioms Application.certificate_transformed
#print axioms Application.transformed_full_constituents
#print axioms Application.finiteSupport
#print axioms Application.curveSupport
#print axioms Application.finiteFourierBound
#print axioms Application.curveFourierBound
#print axioms UniformApplications
#print axioms UniformApplications.mk
#print axioms UniformApplications.rec
#print axioms UniformApplications.recOn
#print axioms UniformApplications.casesOn
#print axioms UniformApplications.noConfusionType
#print axioms UniformApplications.noConfusion
#print axioms UniformApplications.theory
#print axioms UniformApplications.application
#print axioms UniformApplications.stalkCertificates
#print axioms UniformApplications.localFourierHypothesis
#print axioms UniformApplications.hasFiniteExceptionalTypeIIIInput

end PrimeGap182.TypeIII.PublishedTypeIII
