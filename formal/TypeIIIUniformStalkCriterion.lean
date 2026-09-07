import TypeIIIStalkAssembly
import TypeIIISurfaceWeightBounds

/-!
# A uniform conditional arithmetic criterion for the original Type III input

The records below retain explicit surface spectra, trace identities, ordinary
support data, and the standard weight convention. They do not assert that
the spectra come from an etale realization, or that the required support
restrictions follow from published theorems. Those are separate geometric
obligations. No record contains a Fourier norm estimate.

All dimension, degree, support-cardinality, and cutoff constants in the
uniform family are fixed before the prime and all five residue parameters.
The endpoint is the unchanged `LocalFourierHypothesis`, followed by its
original existential formulation `HasFiniteExceptionalTypeIIIInput`.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

/-- The common physical and transformed data for the fifteen nonempty
corrected subproducts of one original residue-parameter tuple. -/
structure TypeIIIStalkCertificate (p : ℕ) [Fact p.Prime]
    (B Dphys Rphys : ℕ) (α m m' n n' : ZMod p) where
  physicalOpen : Finset (ZMod p × ZMod p)
  physical : Finset (Fin 4) → ZMod p → ZMod p → SurfaceStalk
  transformed : Finset (Fin 4) → ZMod p → ZMod p → SurfaceStalk
  physicalExceptional : Finset (Fin 4) → Finset (ZMod p × ZMod p)
  complement_card : (Finset.univ \ physicalOpen).card ≤ 2 * Dphys * p
  physicalExceptional_card : ∀ S ∈ nonemptyCoreSubsets,
    (physicalExceptional S).card ≤ Rphys
  trace_on : ∀ S ∈ nonemptyCoreSubsets, ∀ x y, (x, y) ∈ physicalOpen →
    (physical S x y).trace = ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y
  fourier_trace : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    (transformed S h k).trace = fourier₂ p (fun x y => (physical S x y).trace) h k
  physical_dimensions : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
    (physical S x y).dimensionsLe B
  physical_weights : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
    (physical S x y).weightsLe p ((S.card : ℝ) + 2)
  physical_minusOne : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
    (x, y) ∉ physicalExceptional S → (physical S x y).minusOne.dimension = 0
  physical_zero : ∀ S ∈ nonemptyCoreSubsets, ∀ x y,
    (physical S x y).zero.dimension = 0
  transformed_dimensions : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    (transformed S h k).dimensionsLe B
  transformed_weights : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    (transformed S h k).weightsLe p ((S.card : ℝ) + 4)

/-- The additional ordinary-support data needed in the distinct-index
branch. It concerns the same transformed spectra in the common certificate. -/
structure TypeIIIFiniteStalkSupport {p : ℕ} [Fact p.Prime]
    {B Dphys Rphys : ℕ} {α m m' n n' : ZMod p}
    (certificate : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n')
    (Dcore : ℕ) where
  exceptional : Finset (Fin 4) → Finset (ZMod p × ZMod p)
  exceptional_card : ∀ S ∈ nonemptyCoreSubsets, (exceptional S).card ≤ Dcore
  minusOne : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    (h, k) ∉ exceptional S → (certificate.transformed S h k).minusOne.dimension = 0
  zero : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    (certificate.transformed S h k).zero.dimension = 0

/-- The repeated-index alternative permits a curve in degree minus one
and the origin in degree zero, with actual nonzero defining polynomials. -/
structure TypeIIICurveStalkSupport {p : ℕ} [Fact p.Prime]
    {B Dphys Rphys : ℕ} {α m m' n n' : ZMod p}
    (certificate : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n')
    (Dcore : ℕ) where
  equation : Finset (Fin 4) → MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))
  equation_ne_zero : ∀ S ∈ nonemptyCoreSubsets, equation S ≠ 0
  equation_degree : ∀ S ∈ nonemptyCoreSubsets, (equation S).totalDegree ≤ Dcore
  minusOne : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    planeEval p (equation S) h k ≠ 0 →
      (certificate.transformed S h k).minusOne.dimension = 0
  zero : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
    ¬ (h = 0 ∧ k = 0) → (certificate.transformed S h k).zero.dimension = 0

/-- Exactly the constant in the proved raw stalk assembly. -/
def uniformStalkConstant (B Dphys Rphys : ℕ) : ℝ :=
  81 + 175 * surfaceAssemblyCoreConstant B Dphys Rphys + 13122 * Dphys

theorem uniformStalkConstant_eq (B Dphys Rphys : ℕ) :
    uniformStalkConstant B Dphys Rphys =
      81 + 175 * (B : ℝ) * (1 + 2 * (Dphys : ℝ) + Rphys) + 13122 * Dphys := by
  unfold uniformStalkConstant surfaceAssemblyCoreConstant
  ring

/-- Positivity is unconditional, including a supplied dimension bound zero. -/
theorem uniformStalkConstant_pos (B Dphys Rphys : ℕ) :
    0 < uniformStalkConstant B Dphys Rphys := by
  have hC := surfaceAssemblyCoreConstant_nonneg B Dphys Rphys
  unfold uniformStalkConstant
  positivity

theorem TypeIIIStalkCertificate.physical_eigenvaluesLe
    {p : ℕ} [Fact p.Prime] {B Dphys Rphys : ℕ} {α m m' n n' : ZMod p}
    (c : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n')
    (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) (x y : ZMod p) :
    (c.physical S x y).eigenvaluesLe ((p : ℝ) ^ 2)
      ((p : ℝ) ^ 2 * Real.sqrt p) ((p : ℝ) ^ 3) :=
  (c.physical S x y).core_physical_eigenvaluesLe p (Fact.out : p.Prime).pos S
    (c.physical_weights S hS x y)

theorem TypeIIIStalkCertificate.transformed_eigenvaluesLe
    {p : ℕ} [Fact p.Prime] {B Dphys Rphys : ℕ} {α m m' n n' : ZMod p}
    (c : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n')
    (S : Finset (Fin 4)) (hS : S ∈ nonemptyCoreSubsets) (h k : ZMod p) :
    (c.transformed S h k).eigenvaluesLe ((p : ℝ) ^ 3)
      ((p : ℝ) ^ 3 * Real.sqrt p) ((p : ℝ) ^ 4) :=
  (c.transformed S h k).core_fourier_eigenvaluesLe p (Fact.out : p.Prime).pos S
    (c.transformed_weights S hS h k)

theorem TypeIIIFiniteStalkSupport.fourierBound
    {p : ℕ} [Fact p.Prime] {B Dphys Rphys Dcore : ℕ} {α m m' n n' : ZMod p}
    {c : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n'}
    (support : TypeIIIFiniteStalkSupport c Dcore) (hbase : BaselineLocalInputs)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) :
    FiniteExceptionalFourierBound p (uniformStalkConstant B Dphys Rphys)
      (15 * Dcore) α m m' n n' := by
  unfold uniformStalkConstant
  exact finiteExceptionalFourierBound_of_surface_stalks hbase p B Dphys Rphys Dcore
    c.physicalOpen c.complement_card α m m' n n' hα hm hm' hn hn'
    c.physical c.transformed c.physicalExceptional support.exceptional
    c.physicalExceptional_card support.exceptional_card c.trace_on c.fourier_trace
    c.physical_dimensions c.physical_eigenvaluesLe c.physical_minusOne c.physical_zero
    c.transformed_dimensions c.transformed_eigenvaluesLe support.minusOne support.zero

theorem TypeIIICurveStalkSupport.fourierBound
    {p : ℕ} [Fact p.Prime] {B Dphys Rphys Dcore : ℕ} {α m m' n n' : ZMod p}
    {c : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n'}
    (support : TypeIIICurveStalkSupport c Dcore) (hbase : BaselineLocalInputs)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hn : n ≠ 0) (hn' : n' ≠ 0) :
    CurveExceptionalFourierBound p (uniformStalkConstant B Dphys Rphys)
      (15 * Dcore) α m m' n n' := by
  unfold uniformStalkConstant
  exact curveExceptionalFourierBound_of_surface_stalks hbase p B Dphys Rphys Dcore
    c.physicalOpen c.complement_card α m m' n n' hα hm hm' hn hn'
    c.physical c.transformed c.physicalExceptional support.equation
    c.physicalExceptional_card support.equation_ne_zero support.equation_degree
    c.trace_on c.fourier_trace c.physical_dimensions c.physical_eigenvaluesLe
    c.physical_minusOne c.physical_zero c.transformed_dimensions
    c.transformed_eigenvaluesLe support.minusOne support.zero

/-- A uniform family of conditional certificates. The five natural-number
parameters are fixed before the prime, all residue parameters, and index
distinctness/repetition. No local Fourier estimate is a field. -/
structure UniformTypeIIIStalkCertificates (B Dphys Rphys Dcore p₀ : ℕ) where
  common : ∀ (p : ℕ) [Fact p.Prime], p₀ < p →
    ∀ α m m' n n' : ZMod p,
      α ≠ 0 → m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
        TypeIIIStalkCertificate p B Dphys Rphys α m m' n n'
  finite : ∀ (p : ℕ) [Fact p.Prime] (hp : p₀ < p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0),
    (m ≠ m' ∧ n ≠ n') →
      TypeIIIFiniteStalkSupport (common p hp α m m' n n' hα hm hm' hn hn') Dcore
  curve : ∀ (p : ℕ) [Fact p.Prime] (hp : p₀ < p)
    (α m m' n n' : ZMod p)
    (hα : α ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0),
    (m = m' ∨ n = n') →
      TypeIIICurveStalkSupport (common p hp α m m' n n' hα hm hm' hn hn') Dcore

/-- The original local hypothesis follows from a uniform family of the
explicit stalk certificates, with its exact original parameter quantifiers. -/
theorem localFourierHypothesis_of_uniform_stalk_certificates
    (hbase : BaselineLocalInputs) (B Dphys Rphys Dcore p₀ : ℕ)
    (certificates : UniformTypeIIIStalkCertificates B Dphys Rphys Dcore p₀) :
    LocalFourierHypothesis (uniformStalkConstant B Dphys Rphys) (15 * Dcore) p₀ := by
  intro p _ hp α m m' n n' hα hm hm' hn hn'
  constructor
  · intro hdistinct
    exact (certificates.finite p hp α m m' n n' hα hm hm' hn hn' hdistinct).fourierBound
      hbase hα hm hm' hn hn'
  · intro hrepeated
    exact (certificates.curve p hp α m m' n n' hα hm hm' hn hn' hrepeated).fourierBound
      hbase hα hm hm' hn hn'

/-- The unchanged existential Type III input, conditional on the stated
uniform spectra/trace/weight/support certificates and explicit baseline inputs. -/
theorem hasFiniteExceptionalTypeIIIInput_of_uniform_stalk_certificates
    (hbase : BaselineLocalInputs) (B Dphys Rphys Dcore p₀ : ℕ)
    (certificates : UniformTypeIIIStalkCertificates B Dphys Rphys Dcore p₀) :
    HasFiniteExceptionalTypeIIIInput := by
  exact ⟨uniformStalkConstant B Dphys Rphys, uniformStalkConstant_pos B Dphys Rphys,
    15 * Dcore, p₀,
    localFourierHypothesis_of_uniform_stalk_certificates hbase B Dphys Rphys Dcore p₀
      certificates⟩

#print axioms TypeIIIStalkCertificate
#print axioms TypeIIIStalkCertificate.mk
#print axioms TypeIIIStalkCertificate.rec
#print axioms TypeIIIStalkCertificate.recOn
#print axioms TypeIIIStalkCertificate.casesOn
#print axioms TypeIIIStalkCertificate.noConfusionType
#print axioms TypeIIIStalkCertificate.noConfusion
#print axioms TypeIIIStalkCertificate.physicalOpen
#print axioms TypeIIIStalkCertificate.physical
#print axioms TypeIIIStalkCertificate.transformed
#print axioms TypeIIIStalkCertificate.physicalExceptional
#print axioms TypeIIIStalkCertificate.complement_card
#print axioms TypeIIIStalkCertificate.physicalExceptional_card
#print axioms TypeIIIStalkCertificate.trace_on
#print axioms TypeIIIStalkCertificate.fourier_trace
#print axioms TypeIIIStalkCertificate.physical_dimensions
#print axioms TypeIIIStalkCertificate.physical_weights
#print axioms TypeIIIStalkCertificate.physical_minusOne
#print axioms TypeIIIStalkCertificate.physical_zero
#print axioms TypeIIIStalkCertificate.transformed_dimensions
#print axioms TypeIIIStalkCertificate.transformed_weights
#print axioms TypeIIIFiniteStalkSupport
#print axioms TypeIIIFiniteStalkSupport.mk
#print axioms TypeIIIFiniteStalkSupport.rec
#print axioms TypeIIIFiniteStalkSupport.recOn
#print axioms TypeIIIFiniteStalkSupport.casesOn
#print axioms TypeIIIFiniteStalkSupport.noConfusionType
#print axioms TypeIIIFiniteStalkSupport.noConfusion
#print axioms TypeIIIFiniteStalkSupport.exceptional
#print axioms TypeIIIFiniteStalkSupport.exceptional_card
#print axioms TypeIIIFiniteStalkSupport.minusOne
#print axioms TypeIIIFiniteStalkSupport.zero
#print axioms TypeIIICurveStalkSupport
#print axioms TypeIIICurveStalkSupport.mk
#print axioms TypeIIICurveStalkSupport.rec
#print axioms TypeIIICurveStalkSupport.recOn
#print axioms TypeIIICurveStalkSupport.casesOn
#print axioms TypeIIICurveStalkSupport.noConfusionType
#print axioms TypeIIICurveStalkSupport.noConfusion
#print axioms TypeIIICurveStalkSupport.equation
#print axioms TypeIIICurveStalkSupport.equation_ne_zero
#print axioms TypeIIICurveStalkSupport.equation_degree
#print axioms TypeIIICurveStalkSupport.minusOne
#print axioms TypeIIICurveStalkSupport.zero
#print axioms uniformStalkConstant
#print axioms uniformStalkConstant_eq
#print axioms uniformStalkConstant_pos
#print axioms TypeIIIStalkCertificate.physical_eigenvaluesLe
#print axioms TypeIIIStalkCertificate.transformed_eigenvaluesLe
#print axioms TypeIIIFiniteStalkSupport.fourierBound
#print axioms TypeIIICurveStalkSupport.fourierBound
#print axioms UniformTypeIIIStalkCertificates
#print axioms UniformTypeIIIStalkCertificates.mk
#print axioms UniformTypeIIIStalkCertificates.rec
#print axioms UniformTypeIIIStalkCertificates.recOn
#print axioms UniformTypeIIIStalkCertificates.casesOn
#print axioms UniformTypeIIIStalkCertificates.noConfusionType
#print axioms UniformTypeIIIStalkCertificates.noConfusion
#print axioms UniformTypeIIIStalkCertificates.common
#print axioms UniformTypeIIIStalkCertificates.finite
#print axioms UniformTypeIIIStalkCertificates.curve
#print axioms localFourierHypothesis_of_uniform_stalk_certificates
#print axioms hasFiniteExceptionalTypeIIIInput_of_uniform_stalk_certificates

end PrimeGap182.TypeIII
