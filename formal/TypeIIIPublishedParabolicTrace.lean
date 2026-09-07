import TypeIIIJordanCorrection
import TypeIIICorrectedTraceCovariance

/-!
# The parabolic trace and rank from an actual exact sequence

This file proves finite-dimensional linear algebra. The supplied maps are
the injection from the actual Jordan centralizer into a compact-cohomology
space and the surjection to a parabolic-cohomology space. Exactness and the
Frobenius squares are explicit. Neither the rank nor the corrected trace of
the parabolic space is assumed.

The published geometric inputs that can produce such data are the boundary
cohomology exact sequence, the trace formula, Grothendieck--Ogg--Shafarevich,
and the arithmetic local Kloosterman model. Identifying these supplied
spaces, maps and operators with the particular sheaf family remains a
separate application. This module asserts no such identification, lissity,
local-phase realization, or Type III Fourier estimate.

The dimension-three boundary and its trace use the existing, proved actual
matrix centralizer calculation. The sign twist is applied to the actual
endomorphism, not merely to a name for its trace.
-/

noncomputable section

namespace PrimeGap182.TypeIII.PublishedParabolicTrace

universe u v w z

section ExactTrace

variable {k : Type u} [Field k]
  {U : Type v} [AddCommGroup U] [Module k U]
  {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {W : Type z} [AddCommGroup W] [Module k W]

/-- Trace additivity for the supplied short exact sequence and the
supplied commuting operators. Splittings exist because the coefficients
form a field; neither a splitting nor Frobenius-stability of a complement
is a premise. -/
theorem trace_add_of_short_exact
    (i : U →ₗ[k] V) (pi : V →ₗ[k] W)
    (hi : Function.Injective i) (hpi : Function.Surjective pi)
    (hexact : LinearMap.range i = LinearMap.ker pi)
    (fU : U →ₗ[k] U) (fV : V →ₗ[k] V) (fW : W →ₗ[k] W)
    (hleft : fV.comp i = i.comp fU)
    (hright : pi.comp fV = fW.comp pi) :
    LinearMap.trace k V fV = LinearMap.trace k U fU + LinearMap.trace k W fW := by
  let : FiniteDimensional k U := FiniteDimensional.of_injective i hi
  let : FiniteDimensional k W := FiniteDimensional.of_surjective pi hpi
  obtain ⟨r, hr⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨s, hs⟩ := pi.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hpi)
  have hri (x : U) : r (i x) = x := DFunLike.congr_fun hr x
  have hpis (x : W) : pi (s x) = x := DFunLike.congr_fun hs x
  have hpii (x : U) : pi (i x) = 0 := by
    have hx : i x ∈ LinearMap.range i := ⟨x, rfl⟩
    rw [hexact] at hx
    exact hx
  let r' : V →ₗ[k] U := r.comp (LinearMap.id - s.comp pi)
  have hr'i (x : U) : r' (i x) = x := by
    simp [r', hpii, hri]
  have hir' (x : V) : i (r' x) = x - s (pi x) := by
    have hx : x - s (pi x) ∈ LinearMap.ker pi := by
      change pi (x - s (pi x)) = 0
      simp [hpis]
    rw [← hexact] at hx
    obtain ⟨y, hy⟩ := hx
    change i (r (x - s (pi x))) = x - s (pi x)
    rw [← hy, hri]
  have hsplit : i.comp r' + s.comp pi = LinearMap.id := by
    ext x
    change i (r' x) + s (pi x) = x
    rw [hir']
    abel
  have htraceLeft : r'.comp (fV.comp i) = fU := by
    ext x
    change r' (fV (i x)) = fU x
    rw [show fV (i x) = i (fU x) from DFunLike.congr_fun hleft x, hr'i]
  have htraceRight : pi.comp (fV.comp s) = fW := by
    ext x
    change pi (fV (s x)) = fW x
    rw [show pi (fV (s x)) = fW (pi (s x)) from
      DFunLike.congr_fun hright (s x), hpis]
  calc
    LinearMap.trace k V fV =
        LinearMap.trace k V (fV.comp (i.comp r' + s.comp pi)) := by
      rw [hsplit, LinearMap.comp_id]
    _ = LinearMap.trace k V ((fV.comp i).comp r') +
        LinearMap.trace k V ((fV.comp s).comp pi) := by
      simp only [LinearMap.comp_add, map_add, LinearMap.comp_assoc]
    _ = LinearMap.trace k U (r'.comp (fV.comp i)) +
        LinearMap.trace k W (pi.comp (fV.comp s)) := by
      rw [LinearMap.trace_comp_comm' r' (fV.comp i),
        LinearMap.trace_comp_comm' pi (fV.comp s)]
    _ = _ := by rw [htraceLeft, htraceRight]

end ExactTrace

/-- A literal boundary injection, quotient map and Frobenius actions.
Its intended geometric realization is separate data, not a theorem of
this record. In particular there are no final-rank or final-trace fields. -/
structure JordanBoundaryData {k : Type u} [Field k] (q : k) (hq : q ≠ 0)
    (Vc : Type v) [AddCommGroup Vc] [Module k Vc]
    (Vpar : Type w) [AddCommGroup Vpar] [Module k Vpar] where
  boundary : jordanThreeCentralizer k →ₗ[k] Vc
  quotient : Vc →ₗ[k] Vpar
  boundary_injective : Function.Injective boundary
  quotient_surjective : Function.Surjective quotient
  exact : LinearMap.range boundary = LinearMap.ker quotient
  compactFrobenius : Vc →ₗ[k] Vc
  parabolicFrobenius : Vpar →ₗ[k] Vpar
  boundary_frobenius : compactFrobenius.comp boundary =
    boundary.comp (jordanThreeCentralizerConjugation q hq)
  quotient_frobenius : quotient.comp compactFrobenius =
    parabolicFrobenius.comp quotient

namespace JordanBoundaryData

variable {k : Type u} [Field k] {q : k} {hq : q ≠ 0}
  {Vc : Type v} [AddCommGroup Vc] [Module k Vc] [FiniteDimensional k Vc]
  {Vpar : Type w} [AddCommGroup Vpar] [Module k Vpar]
  (D : JordanBoundaryData q hq Vc Vpar)

include D

/-- Finite dimensionality of the target follows from the original
surjection; it is not an extra premise. -/
theorem finiteDimensional : FiniteDimensional k Vpar :=
  FiniteDimensional.of_surjective D.quotient D.quotient_surjective

/-- The rank loss is exactly the computed centralizer dimension. -/
theorem finrank_add : Module.finrank k Vpar + 3 = Module.finrank k Vc := by
  have h := D.quotient.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr D.quotient_surjective,
    finrank_top, ← D.exact,
    LinearMap.finrank_range_of_inj D.boundary_injective,
    jordanThreeCentralizer_finrank] at h
  exact h

/-- Rank six is deduced from compact rank nine and the original exact
sequence, rather than supplied as the rank of a named core. -/
theorem finrank_eq_six (hc : Module.finrank k Vc = 9) :
    Module.finrank k Vpar = 6 := by
  have h := D.finrank_add
  omega

/-- The original parabolic Frobenius has the stated trace defect. -/
theorem trace_add :
    LinearMap.trace k Vc D.compactFrobenius =
      (1 + q⁻¹ + q⁻¹ ^ 2) + LinearMap.trace k Vpar D.parabolicFrobenius := by
  rw [trace_add_of_short_exact D.boundary D.quotient
    D.boundary_injective D.quotient_surjective D.exact
    (jordanThreeCentralizerConjugation q hq) D.compactFrobenius
    D.parabolicFrobenius D.boundary_frobenius D.quotient_frobenius,
    jordanThreeCentralizerConjugation_trace]

/-- Specializing the compact-support trace formula gives the full
negative correction for the parabolic image. -/
theorem trace_eq (c : k)
    (hc : LinearMap.trace k Vc D.compactFrobenius = -c) :
    LinearMap.trace k Vpar D.parabolicFrobenius = -(c + (1 + q⁻¹ + q⁻¹ ^ 2)) := by
  have h := D.trace_add
  rw [hc] at h
  linear_combination -h

/-- The constant sign sheaf acts on the actual operator by `(-1)^d`.
The resulting correction has exponent `d+1` over degree-d extensions. -/
theorem signed_trace_eq (d : ℕ) (c : k)
    (hc : LinearMap.trace k Vc D.compactFrobenius = -c) :
    LinearMap.trace k Vpar (((-1 : k) ^ d) • D.parabolicFrobenius) =
      (-1 : k) ^ (d + 1) * (c + (1 + q⁻¹ + q⁻¹ ^ 2)) := by
  rw [map_smul, smul_eq_mul, D.trace_eq c hc, pow_succ]
  ring

end JordanBoundaryData

section FiniteField

open FiniteFieldSums

variable (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] [Fintype L]
  [Algebra (ZMod p) L]

/-- The complex normalization denominator is nonzero for a finite field. -/
theorem complexCard_ne_zero : (Fintype.card L : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

variable {Vc : Type v} [AddCommGroup Vc] [Module ℂ Vc] [FiniteDimensional ℂ Vc]
  {Vpar : Type w} [AddCommGroup Vpar] [Module ℂ Vpar]
  (D : JordanBoundaryData (Fintype.card L : ℂ) (complexCard_ne_zero L) Vc Vpar)

/-- All-extension signed correlation trace for the actual parabolic
operator, conditional on the original compact-cohomology trace formula. -/
theorem signed_correlation_trace (A B : L)
    (hc : LinearMap.trace ℂ Vc D.compactFrobenius =
      -FiniteFieldSums.correlation (traceAddChar p L) A B 1) :
    LinearMap.trace ℂ Vpar
      (((-1 : ℂ) ^ Module.finrank (ZMod p) L) • D.parabolicFrobenius) =
        extensionSign p L * (FiniteFieldSums.correlation (traceAddChar p L) A B 1 +
          FiniteFieldSums.coreCorrection L) := by
  exact D.signed_trace_eq (Module.finrank (ZMod p) L)
    (FiniteFieldSums.correlation (traceAddChar p L) A B 1) hc

/-- The nonlinear torus coordinates and the same zero-extended kernel
are retained. On the torus the trace is exactly the signed corrected
kernel used in `expectedTrace`. -/
theorem signed_kernel_trace (α m n x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (hc : LinearMap.trace ℂ Vc D.compactFrobenius =
      -FiniteFieldSums.correlation (traceAddChar p L) (α * y / (m * x ^ 2))
        (α * x / (n * y ^ 2)) 1) :
    LinearMap.trace ℂ Vpar
      (((-1 : ℂ) ^ Module.finrank (ZMod p) L) • D.parabolicFrobenius) =
        extensionSign p L * FiniteFieldSums.correctedKernel
          (traceAddChar p L) α m n x y := by
  rw [signed_correlation_trace p L D _ _ hc]
  simp only [FiniteFieldSums.correctedKernel, FiniteFieldSums.kernel,
    ite_eq_right (not_or.mpr ⟨hx, hy⟩)]

end FiniteField

end PrimeGap182.TypeIII.PublishedParabolicTrace

#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.trace_add_of_short_exact
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.mk
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.rec
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.recOn
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.boundary
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.quotient
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.boundary_injective
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.quotient_surjective
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.exact
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.compactFrobenius
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.parabolicFrobenius
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.boundary_frobenius
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.quotient_frobenius
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.finiteDimensional
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.finrank_add
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.finrank_eq_six
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.trace_add
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.trace_eq
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.JordanBoundaryData.signed_trace_eq
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.complexCard_ne_zero
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.signed_correlation_trace
#print axioms PrimeGap182.TypeIII.PublishedParabolicTrace.signed_kernel_trace
