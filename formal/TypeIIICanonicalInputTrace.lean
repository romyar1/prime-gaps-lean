import TypeIIICanonicalCurveInput

/-!
# Traces of the canonical input recipe

Trace compatibility with pullback is supplied for every affine-line map
and source object at the chosen parameter point. Applying the proved
coordinate formulas gives the three original Kloosterman/AS traces.
The same canonical input therefore has both the geometric properties
and the arithmetic point trace required by the physical construction.

Only the one-variable source trace formulas and general pullback/tensor/
dual laws are inputs. In particular, no trace of a finished correlation
or cohomological core is assumed. The Kl3 source formula is required only
on units: no formula at the zero-extension boundary is silently imposed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.CanonicalInputTrace

open StartingSourceMaps StartingSourceComplexity CanonicalCurveInput
open PublishedPhysicalConstruction

universe u v w
variable {k : Type} [Field k] {L : Type} [Field L] [Fintype L] [Algebra k L]
  {Input : Type u} {Point : Type v} {LineObj : Type w}
  {D : CurveData Input Point}

/-- General trace/pullback compatibility at the parameter point (lambda,xi).
The rule ranges over all algebraic maps to A1 and all source objects. -/
structure PullbackTraceRules (F : PullbackData k LineObj Input)
    (T : CurveTraceData D L) (lineTrace : LineObj → L → ℂ) (lambda xi : Lˣ) : Prop where
  pullback : ∀ (g : MvPolynomial (Fin 1) k →ₐ[k] SourceRing k) A x,
    T.trace (F.pullback (Spec.map (CommRingCat.ofHom g.toRingHom)) A) x =
      lineTrace A (evaluation (K := k) x lambda xi (g (X 0)))

variable (F : PullbackData k LineObj Input) (G : LineGeometry LineObj)
  (R : ScalarPullbackRules F G D) (kl as : LineObj)
  (hkl : Kl3Properties G kl) (has : ASProperties G as)
  (T : CurveTraceData D L) (lineTrace : LineObj → L → ℂ) (lambda xi : Lˣ)
  (Q : PullbackTraceRules F T lineTrace lambda xi) (ψ : AddChar L ℂ)
  (hklTrace : ∀ x : Lˣ, lineTrace kl (x : L) = FiniteFieldSums.kl3 ψ (x : L))
  (hASTrace : ∀ x : L, lineTrace as x = ψ x)

include Q hklTrace hASTrace in
/-- The formerly supplied three family traces follow from the actual maps. -/
theorem canonicalTraceData :
    KloostermanTraceData D L (canonicalInput F G R kl as hkl has) T ψ lambda xi where
  first_trace x := by
    change T.trace (F.pullback (inputMorphism k 0) kl) x = _
    rw [inputMorphism, Q.pullback, inputHom_evaluation]
    exact hklTrace x
  second_trace x := by
    change T.trace (F.pullback (inputMorphism k 1) kl) x = _
    rw [inputMorphism, Q.pullback, inputHom_evaluation]
    exact hklTrace (lambda * x)
  additive_trace x := by
    change T.trace (F.pullback (inputMorphism k 2) as) x = _
    rw [inputMorphism, Q.pullback, inputHom_evaluation]
    exact hASTrace ((xi : L) * x)

include Q hklTrace hASTrace in
/-- The trace of the same literal rank-nine tensor, before cohomology. -/
theorem canonical_input_trace
    (tensorTrace : ∀ A B x, T.trace (D.tensor A B) x = T.trace A x * T.trace B x)
    (dualTrace : ∀ A, D.Lisse A → D.Pure A 0 → ∀ x,
      T.trace (D.dual A) x = star (T.trace A x))
    (x : Lˣ) :
    T.trace (canonicalInput F G R kl as hkl has).input x =
      FiniteFieldSums.kl3 ψ (x : L) * star (FiniteFieldSums.kl3 ψ (lambda * (x : L))) *
        ψ (xi * (x : L)) := by
  let K := canonicalInput F G R kl as hkl has
  have A := canonicalTraceData F G R kl as hkl has T lineTrace lambda xi Q ψ hklTrace hASTrace
  change T.trace (D.tensor (D.tensor K.first (D.dual K.second)) K.additive) x = _
  rw [tensorTrace, tensorTrace, dualTrace K.second K.second_lisse K.second_pure,
    A.first_trace, A.second_trace, A.additive_trace]

end PrimeGap182.TypeIII.CanonicalInputTrace

#print axioms PrimeGap182.TypeIII.CanonicalInputTrace.canonicalTraceData
#print axioms PrimeGap182.TypeIII.CanonicalInputTrace.canonical_input_trace
