import Mathlib

/-! Constant-field descent for the Type III coefficient argument.

These results concern actual field automorphisms. They do not construct the
sheaf or prove that its wild coefficients form an invariant finite set.
-/

noncomputable section
open scoped Classical

namespace PrimeGap182.TypeIII

set_option maxHeartbeats 1000000

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [IsAlgClosed L]

theorem exists_algEquiv_of_singleton_transcendence_bases {x y : L}
    (hx : IsTranscendenceBasis k (fun _ : Unit => x))
    (hy : IsTranscendenceBasis k (fun _ : Unit => y)) :
    ∃ σ : L ≃ₐ[k] L, σ x = y := by
  let Sx := Algebra.adjoin k (Set.range (fun _ : Unit => x))
  let Sy := Algebra.adjoin k (Set.range (fun _ : Unit => y))
  let e : Sx ≃ₐ[k] Sy := hx.1.aevalEquiv.symm.trans hy.1.aevalEquiv
  let : IsAlgClosure Sx L :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis (fun _ : Unit => x) hx
  let : IsAlgClosure Sy L :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis (fun _ : Unit => y) hy
  let ρ : L ≃+* L := IsAlgClosure.equivOfEquiv L L e.toRingEquiv
  have hρ (s : Sx) : ρ (algebraMap Sx L s) = algebraMap Sy L (e s) :=
    IsAlgClosure.equivOfEquiv_algebraMap L L e.toRingEquiv s
  have hbase (c : k) : ρ (algebraMap k L c) = algebraMap k L c := by
    simpa only [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply] using
      hρ (algebraMap k Sx c)
  refine ⟨AlgEquiv.ofRingEquiv hbase, ?_⟩
  have hgen := hρ (hx.1.aevalEquiv (MvPolynomial.X ()))
  have hxgen : algebraMap Sx L (hx.1.aevalEquiv (MvPolynomial.X ())) = x := by
    simpa only [MvPolynomial.aeval_X] using
      hx.1.algebraMap_aevalEquiv (MvPolynomial.X ())
  have hygen : algebraMap Sy L (hy.1.aevalEquiv (MvPolynomial.X ())) = y := by
    simpa only [MvPolynomial.aeval_X] using
      hy.1.algebraMap_aevalEquiv (MvPolynomial.X ())
  change ρ x = y
  simpa only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    hxgen, hygen] using hgen

omit [IsAlgClosed L] in
theorem singleton_transcendence_basis_of_trdeg_le_one
    (hdeg : Algebra.trdeg k L ≤ 1) {x : L} (hx : Transcendental k x) :
    IsTranscendenceBasis k (fun _ : Unit => x) := by
  have hi : AlgebraicIndependent k (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  exact hi.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using hdeg)

theorem infinite_algEquiv_orbit_of_transcendental [Infinite k]
    (hdeg : Algebra.trdeg k L ≤ 1) {x : L} (hx : Transcendental k x) :
    (Set.range (fun σ : L ≃ₐ[k] L => σ x)).Infinite := by
  have hxbase := singleton_transcendence_basis_of_trdeg_le_one hdeg hx
  have hinj : Function.Injective (fun c : k => x + algebraMap k L c) := by
    intro a b hab
    exact (algebraMap k L).injective (add_left_cancel hab)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨c, rfl⟩
  have hy : Transcendental k (x + algebraMap k L c) := by
    intro ha
    apply hx
    simpa only [add_sub_cancel_right] using ha.sub (isAlgebraic_algebraMap c)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_singleton_transcendence_bases hxbase
    (singleton_transcendence_basis_of_trdeg_le_one hdeg hy)
  exact ⟨σ, hσ⟩

omit [IsAlgClosed L] in
theorem exists_constant_of_isAlgebraic [IsAlgClosed k] {x : L}
    (hx : IsAlgebraic k x) : ∃ c : k, algebraMap k L c = x := by
  have hi : IsIntegral k x := hx.isIntegral
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hi
  have hd : (minpoly k x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi)
  have he : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hq, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly k x).coeff 0, by simpa only [map_neg] using he.symm⟩

theorem finite_algEquiv_orbit_iff_constant [IsAlgClosed k]
    (hdeg : Algebra.trdeg k L ≤ 1) (x : L) :
    (Set.range (fun σ : L ≃ₐ[k] L => σ x)).Finite ↔
      ∃ c : k, algebraMap k L c = x := by
  constructor
  · intro hfinite
    by_cases ha : IsAlgebraic k x
    · exact exists_constant_of_isAlgebraic ha
    · exact False.elim ((infinite_algEquiv_orbit_of_transcendental hdeg ha) hfinite)
  · rintro ⟨c, rfl⟩
    simp only [AlgEquiv.commutes, Set.range_const, Set.finite_singleton]

theorem constant_of_mem_finite_invariant_set [IsAlgClosed k]
    (hdeg : Algebra.trdeg k L ≤ 1) (s : Set L) (hs : s.Finite)
    (hstable : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ s, σ x ∈ s)
    {x : L} (hx : x ∈ s) : ∃ c : k, algebraMap k L c = x := by
  apply (finite_algEquiv_orbit_iff_constant hdeg x).mp
  apply hs.subset
  rintro _ ⟨σ, rfl⟩
  exact hstable σ x hx

section RationalClosure

variable (K : Type*) [Field K]

theorem rationalAlgebraicClosure_trdeg :
    Algebra.trdeg K (AlgebraicClosure (RatFunc K)) = 1 := by
  let : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors (Polynomial K))
  have h₀ := IsTranscendenceBasis.polynomial Unit K
  have h₁ := h₀.algebraMap_comp (A := RatFunc K)
  have h₂ := h₁.algebraMap_comp (A := AlgebraicClosure (RatFunc K))
  simpa using h₂.lift_cardinalMk_eq_trdeg.symm

theorem rationalAlgebraicClosure_finite_orbit_iff [IsAlgClosed K]
    (x : AlgebraicClosure (RatFunc K)) :
    (Set.range (fun σ : AlgebraicClosure (RatFunc K) ≃ₐ[K]
      AlgebraicClosure (RatFunc K) => σ x)).Finite ↔
      ∃ c : K, algebraMap K (AlgebraicClosure (RatFunc K)) c = x :=
  finite_algEquiv_orbit_iff_constant (rationalAlgebraicClosure_trdeg K).le x

end RationalClosure

#print axioms exists_algEquiv_of_singleton_transcendence_bases
#print axioms infinite_algEquiv_orbit_of_transcendental
#print axioms finite_algEquiv_orbit_iff_constant
#print axioms constant_of_mem_finite_invariant_set
#print axioms rationalAlgebraicClosure_trdeg
#print axioms rationalAlgebraicClosure_finite_orbit_iff

end PrimeGap182.TypeIII
