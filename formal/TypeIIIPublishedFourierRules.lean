import TypeIIIPublishedSupportRules
import TypeIIIInvariantSupportComponents
import TypeIIILinePhaseDescent

/-!
# Conditional local Fourier rules and the rectangle support exclusion

The records in this file are explicit hypotheses about an abstract model of
perverse sheaves and their generic radial inertia. They are not global Lean
axioms and do not instantiate the unfinished foundational adic construction.

The generic Fourier rules translate inversion, linear-map compatibility and
preservation of simple constituents (Laumon, Theorems 1.2.2.1, 1.2.2.4 and
1.3.2.3). The inertia rules translate exact restriction to wild inertia,
uniqueness of pole-one Artin--Schreier characters, and base change for a
one-variable object defined over the algebraically closed constant field.
The latter gives invariance of a RESCALED phase set, not constancy of a
selected branch. Finite-set descent and the ensuing contradiction are proved.

The family's actual phase realization and coefficient covariance remain
separate premises of the final theorem. In particular no general rule below
mentions Kloosterman sums, rectangle parameters, or a Fourier norm bound.
-/

noncomputable section
open scoped Classical

namespace PrimeGap182.TypeIII.PublishedFourierRules

open PublishedSupportRules

universe u v w

variable {K : Type u} [Field K] [IsAlgClosed K]
  {Obj : Type v} {CurveObj : Type w}

/-- Operations and radial observables. `inverse` is the genuine Fourier
quasi-inverse, including reflection and Tate twist. `linearPullback v J`
is the perverse-normalized pullback `π_v^* J[1]` of a perverse curve object.
`HasSimpleRadialPhases` refers to radial inertia at t=0: after t=T^2,
wild inertia is a direct sum of characters AS(beta/T), allowing coefficient
zero for tame summands. An inverse punctual transform restricts to AS(c*T^2),
which is unramified at this origin, including for a nonzero punctual support.
The profile is an explicit predicate. -/
structure FourierData (K : Type u) [Field K] (Obj : Type v) (CurveObj : Type w) where
  fourier : Obj → Obj
  inverse : Obj → Obj
  linearPullback : (K × K) → CurveObj → Obj
  HasSimpleRadialPhases : Obj → Prop
  phases : Obj → Set (AlgebraicClosure (RatFunc K))

/-- Generic published Fourier-functor and local-representation rules.
The inverse-constituent comparison is only up to isomorphism, since a
chosen constituent list need not contain a literal inverse-image object. -/
structure LocalRules (D : SurfaceData K Obj) (T : CoefficientTransport D)
    (F : FourierData K Obj CurveObj) : Prop where
  support_isomorphic : ∀ {A B}, T.Isomorphic A B → D.support A = D.support B
  profile_isomorphic : ∀ {A B}, T.Isomorphic A B →
    (F.HasSimpleRadialPhases A ↔ F.HasSimpleRadialPhases B)
  phases_isomorphic : ∀ {A B}, T.Isomorphic A B → F.phases A = F.phases B
  inverse_constituent : ∀ P C, C ∈ D.constituents (F.fourier P) →
    ∃ A ∈ D.constituents P, T.Isomorphic (F.inverse C) A
  profile_constituent : ∀ P A, F.HasSimpleRadialPhases P →
    A ∈ D.constituents P → F.HasSimpleRadialPhases A
  phases_constituent : ∀ P A, F.HasSimpleRadialPhases P →
    A ∈ D.constituents P → F.phases A ⊆ F.phases P
  phases_nonempty : ∀ A, F.HasSimpleRadialPhases A →
    D.support A = Set.univ → (F.phases A).Nonempty
  inverse_point_zero_phase : ∀ C, D.Simple C → ∀ z : K × K,
    D.support C = {z} → (0 : AlgebraicClosure (RatFunc K)) ∈ F.phases (F.inverse C)
  inverse_line_pullback : ∀ C, D.Simple C → ∀ a b : K,
    (a ≠ 0 ∨ b ≠ 0) → D.support C ⊆ ScalingLines.originLine a b →
    ∃ J : CurveObj, T.Isomorphic (F.inverse C) (F.linearPullback (b, -a) J)
  linear_pullback_phase_baseChange : ∀ J : CurveObj, ∀ a b : K,
    (a, b) ≠ (0, 0) → F.HasSimpleRadialPhases (F.linearPullback (a, b) J) →
    ∀ u : AlgebraicClosure (RatFunc K),
      u ^ 2 = algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K))
        (RatFunc.C a + RatFunc.C b * RatFunc.X) →
      ∀ σ : AlgebraicClosure (RatFunc K) ≃ₐ[K] AlgebraicClosure (RatFunc K),
        ∀ x ∈ (fun β => u * β) '' F.phases (F.linearPullback (a, b) J),
          σ x ∈ (fun β => u * β) '' F.phases (F.linearPullback (a, b) J)

variable {D : SurfaceData K Obj} {T : CoefficientTransport D}
  {F : FourierData K Obj CurveObj}

omit [IsAlgClosed K] in
/-- Exact restriction and Fourier equivalence pass the supplied full
profile to the inverse transform of any transformed constituent. -/
theorem inverse_constituent_profile (R : LocalRules D T F)
    (P C : Obj) (hC : C ∈ D.constituents (F.fourier P))
    (hfull : D.NoProperConstituents P) (hprofile : F.HasSimpleRadialPhases P) :
    D.support (F.inverse C) = Set.univ ∧
      F.HasSimpleRadialPhases (F.inverse C) ∧ F.phases (F.inverse C) ⊆ F.phases P := by
  obtain ⟨A, hA, hIso⟩ := R.inverse_constituent P C hC
  refine ⟨(R.support_isomorphic hIso).trans (hfull A hA),
    (R.profile_isomorphic hIso).mpr (R.profile_constituent P A hprofile hA), ?_⟩
  rw [R.phases_isomorphic hIso]
  exact R.phases_constituent P A hprofile hA

omit [IsAlgClosed K] in
/-- A punctual Fourier constituent would give the zero radial phase.
The exclusion of that phase is proved for the entire actual rectangle
list, rather than assumed as a Fourier-support statement. -/
theorem no_punctual_constituent_of_rectangle_phases
    (B : BBDRules D) (R : LocalRules D T F)
    (P : Obj) (hfull : D.NoProperConstituents P)
    (hprofile : F.HasSimpleRadialPhases P)
    (h2 : (2 : K) ≠ 0) (α : K) (hα : α ≠ 0) (m n : Fin 2 → K)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty)
    (hphases : F.phases P ⊆ rectangleAllowedPhases α m n s)
    (C : Obj) (hC : C ∈ D.constituents (F.fourier P)) (z : K × K) :
    D.support C ≠ {z} := by
  intro hz
  have hsub := (inverse_constituent_profile R P C hC hfull hprofile).2.2
  exact zero_not_mem_rectangleAllowedPhases h2 α hα m n hm hn hminj hninj s hs
    (hphases (hsub (R.inverse_point_zero_phase C (B.constituent_simple _ C hC) z hz)))

/-- The origin-line case uses the generic linear-map Fourier formula,
constant-field base change and the proved finite-set phase obstruction. -/
theorem no_origin_line_constituent_of_rectangle_phases
    (B : BBDRules D) (R : LocalRules D T F)
    (P : Obj) (hfull : D.NoProperConstituents P)
    (hprofile : F.HasSimpleRadialPhases P)
    (h2 : (2 : K) ≠ 0) (α : K) (hα : α ≠ 0) (m n : Fin 2 → K)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty)
    (hphases : F.phases P ⊆ rectangleAllowedPhases α m n s)
    (C : Obj) (hC : C ∈ D.constituents (F.fourier P))
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ D.support C ⊆ ScalingLines.originLine a b := by
  intro hline
  obtain ⟨hInvFull, hInvProfile, hInvPhases⟩ :=
    inverse_constituent_profile R P C hC hfull hprofile
  obtain ⟨J, hIso⟩ := R.inverse_line_pullback C (B.constituent_simple _ C hC) a b hab hline
  have hdir : (b, -a) ≠ (0, 0) := by
    intro h
    have hb : b = 0 := congrArg Prod.fst h
    have ha : a = 0 := neg_eq_zero.mp (congrArg Prod.snd h)
    exact hab.elim (fun h => h ha) (fun h => h hb)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K))
      (RatFunc.C b + RatFunc.C (-a) * RatFunc.X)) (by decide : 0 < (2 : ℕ))
  have hu0 := linearDirectionRoot_ne_zero b (-a) hdir u hu
  have hstable := R.linear_pullback_phase_baseChange J b (-a) hdir
    ((R.profile_isomorphic hIso).mp hInvProfile) u hu
  rw [← R.phases_isomorphic hIso] at hstable
  exact rectangleAllowedPhases_no_nonempty_rescaled_invariant_subset
    h2 α hα m n hm hn hminj hninj s hs b (-a) u hu0 hu
    (F.phases (F.inverse C)) (R.phases_nonempty _ hInvProfile hInvFull)
    (hInvPhases.trans hphases) hstable

/-- The full constituent exclusion from generic published rules and
separate actual-family phase/covariance data. No new geometric curve-to-line
theorem or Fourier inequality is among the premises. -/
theorem no_proper_constituents_of_rectangle_phases
    {p : ℕ} [CharP K p] (B : BBDRules D) (Q : QSTRules D)
    (S : SupportClassification D) (R : LocalRules D T F)
    (P : Obj) (hfull : D.NoProperConstituents P)
    (hprofile : F.HasSimpleRadialPhases P)
    (h2 : (2 : K) ≠ 0) (α : K) (hα : α ≠ 0) (m n : Fin 2 → K)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty)
    (hphases : F.phases P ⊆ rectangleAllowedPhases α m n s)
    (eight : Kˣ) (height : (eight : K) = 8)
    (hcov : T.Isomorphic (T.coefficient (F.fourier P)) (T.dilate eight (F.fourier P)))
    (hp : 8 ^ Q.properDegreeBound (D.complexity (F.fourier P)) < p) :
    D.NoProperConstituents (F.fourier P) := by
  intro C hC
  by_contra hproper
  rcases S.proper_simple_support C (B.constituent_simple _ C hC) hproper with hpoint | hcurve
  · obtain ⟨z, hz⟩ := hpoint
    exact no_punctual_constituent_of_rectangle_phases B R P hfull hprofile
      h2 α hα m n hm hn hminj hninj s hs hphases C hC z hz
  · obtain ⟨f, hf, hsupport⟩ := hcurve
    obtain ⟨g, hg, hdeg, hvan⟩ := Q.properSupport_polynomial (F.fourier P)
    have hinv : ∀ z ∈ D.properSupportUnion (F.fourier P),
        ((8 : K) * z.1, (8 : K) * z.2) ∈ D.properSupportUnion (F.fourier P) := by
      simpa only [planeDilation_apply, height] using
        properSupportUnion_invariant_of_covariance T (F.fourier P) eight hcov
    have hsub : ∀ x : Fin 2 → K, MvPolynomial.eval x f = 0 →
        (x 0, x 1) ∈ D.properSupportUnion (F.fourier P) := by
      intro x hx
      apply (D.mem_properSupportUnion _ _).mpr
      refine ⟨C, hC, hproper, ?_⟩
      rw [hsupport]
      change MvPolynomial.eval ![x 0, x 1] f = 0
      have he : ![x 0, x 1] = x := by
        funext i
        fin_cases i <;> rfl
      rwa [he]
    obtain ⟨a, b, hab, hline⟩ :=
      InvariantSupportComponents.curve_component_in_origin_line _ hp g hg hdeg
        (D.properSupportUnion (F.fourier P)) hinv hvan f hf hsub
    apply no_origin_line_constituent_of_rectangle_phases B R P hfull hprofile
      h2 α hα m n hm hn hminj hninj s hs hphases C hC a b hab
    intro z hz
    rw [hsupport] at hz
    exact hline ![z.1, z.2] hz

#print axioms FourierData
#print axioms FourierData.mk
#print axioms FourierData.fourier
#print axioms FourierData.inverse
#print axioms FourierData.linearPullback
#print axioms FourierData.HasSimpleRadialPhases
#print axioms FourierData.phases
#print axioms LocalRules
#print axioms LocalRules.mk
#print axioms LocalRules.support_isomorphic
#print axioms LocalRules.profile_isomorphic
#print axioms LocalRules.phases_isomorphic
#print axioms LocalRules.inverse_constituent
#print axioms LocalRules.profile_constituent
#print axioms LocalRules.phases_constituent
#print axioms LocalRules.phases_nonempty
#print axioms LocalRules.inverse_point_zero_phase
#print axioms LocalRules.inverse_line_pullback
#print axioms LocalRules.linear_pullback_phase_baseChange
#print axioms inverse_constituent_profile
#print axioms no_punctual_constituent_of_rectangle_phases
#print axioms no_origin_line_constituent_of_rectangle_phases
#print axioms no_proper_constituents_of_rectangle_phases

end PrimeGap182.TypeIII.PublishedFourierRules
