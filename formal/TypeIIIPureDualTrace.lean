import TypeIIIPointTraceFromTensor

/-!
# Pure dual traces from the actual Frobenius spectra

Purity bounds and the general lisse dual/Tate spectral rule refer to the
characteristic polynomials of the original point-stalk operators. Trace
is their root sum, with algebraic multiplicity. No semisimplicity or new
choice of Frobenius is assumed. Weil II 1.1.12, 1.2.5(ii),(iv), and 1.2.6
supply the representation, dual/twist and fixed-embedding purity scope.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped MonoidalCategory Classical

namespace PrimeGap182.TypeIII.PureDualTrace
open SourceInverseImageSystem RationalPointStalks PublishedPhysicalConstruction

universe mu
variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)} (R : Data B)

/-- The actual characteristic roots, counted with algebraic multiplicity. -/
def eigenvalues (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X) : Multiset ℂ := by
  letI := R.finite E X x A
  exact (LinearMap.charpoly ((R.frobenius E X x).app A).hom).roots

/-- Mathlib's finite-dimensional characteristic-polynomial trace theorem. -/
theorem trace_eigenvalues (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X) :
    R.trace E x A = (eigenvalues R E X x A).sum := by
  let := R.finite E X x A
  exact Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)

/-- The general fixed-embedding weight condition on the same original
operator. Real weights are retained; the application uses zero and one. -/
structure Weights (X : Space (ZMod p)) (Pure : B.Obj X → ℝ → Prop) : Prop where
  weight : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) A w, Pure A w →
    ∀ z ∈ eigenvalues R E X x A, Complex.normSq z = (Fintype.card E : ℝ) ^ w

/-- General spectrum of the lisse ordinary dual followed by twist (-n).
Both multisets are read from the supplied sheaves' actual Frobenius.
This rule precedes purity and preserves algebraic multiplicities. -/
structure DualSpectrum (X : Space (ZMod p)) (dual : (B.Obj X)ᵒᵖ ⥤ B.Obj X)
    (Lisse : B.Obj X → Prop) (n : ℕ) : Prop where
  roots : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) A, Lisse A →
    eigenvalues R E X x (dual.obj (op A)) =
      (eigenvalues R E X x A).map (fun z => (Fintype.card E : ℂ) ^ n / z)

/-- Positive squared modulus turns the dual/Tate eigenvalue into conjugation. -/
theorem quotient_eq_star {q : ℝ} (hq : 0 < q) {z : ℂ} (hz : Complex.normSq z = q) :
    (q : ℂ) / z = star z := by
  have hn : z ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hz
    linarith
  apply (div_eq_iff hn).mpr
  rw [mul_comm, ← hz]
  exact (Complex.mul_conj z).symm

variable {R} {X : Space (ZMod p)} {Pure : B.Obj X → ℝ → Prop}
  {Lisse : B.Obj X → Prop} {dual : (B.Obj X)ᵒᵖ ⥤ B.Obj X} {n : ℕ}

/-- The pure dual(-n) trace follows without diagonalizability, from
the general spectral rule and the original eigenvalue weight bounds. -/
theorem dual_trace (W : Weights R X Pure) (D : DualSpectrum R X dual Lisse n)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X)
    (hA : Lisse A) (hpure : Pure A (n : ℝ)) :
    R.trace E x (dual.obj (op A)) = star (R.trace E x A) := by
  rw [trace_eigenvalues R E X x, trace_eigenvalues R E X x, D.roots E x A hA]
  change _ = (starRingEnd ℂ) (eigenvalues R E X x A).sum
  rw [map_multiset_sum]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z hz
  have hw : Complex.normSq z = (Fintype.card E : ℝ) ^ n := by
    simpa only [Real.rpow_natCast] using W.weight E x A (n : ℝ) hpure z hz
  have hq : (0 : ℝ) < (Fintype.card E : ℝ) ^ n :=
    pow_pos (by exact_mod_cast Fintype.card_pos) n
  change (Fintype.card E : ℂ) ^ n / z = star z
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using quotient_eq_star hq hw

/-- The six retained torus geometric laws, without a trace hypothesis. -/
structure TorusGeometry (P : ParameterData (B.Obj .torus)) : Prop where
  pullback_lisse : ∀ f A, P.Lisse A → P.Lisse ((B.torusOperations.pullback f).obj A)
  pullback_pure : ∀ f A a, P.Pure A a → P.Pure ((B.torusOperations.pullback f).obj A) a
  unit_lisse : P.Lisse (𝟙_ (B.Obj .torus))
  unit_pure : P.Pure (𝟙_ (B.Obj .torus)) 0
  tensor_lisse : ∀ A C, P.Lisse A → P.Lisse C → P.Lisse (A ⊗ C)
  tensor_pure : ∀ A C a b, P.Pure A a → P.Pure C b → P.Pure (A ⊗ C) (a + b)

/-- Instantiate twist -1 and weight one on the exact parameter dual functor. -/
theorem torusGeometryRules (P : ParameterData (B.Obj .torus))
    (DT : (B.Obj .torus)ᵒᵖ ⥤ B.Obj .torus)
    (hDT : ∀ A, P.dualTateMinusOne A = DT.obj (op A))
    (G : TorusGeometry P) (W : Weights R .torus P.Pure)
    (D : DualSpectrum R .torus DT P.Lisse 1) :
    PointTraceFromTensor.TorusGeometryRules R P where
  pullback_lisse := G.pullback_lisse
  pullback_pure := G.pullback_pure
  unit_lisse := G.unit_lisse
  unit_pure := G.unit_pure
  tensor_lisse := G.tensor_lisse
  tensor_pure := G.tensor_pure
  dualTate_trace A hA hw E _ _ _ x y := by
    rw [hDT]
    exact dual_trace W D E (PhysicalTorusMorphism.schemePoint x y) A hA (by simpa using hw)

end PrimeGap182.TypeIII.PureDualTrace

#print axioms PrimeGap182.TypeIII.PureDualTrace.eigenvalues
#print axioms PrimeGap182.TypeIII.PureDualTrace.trace_eigenvalues
#print axioms PrimeGap182.TypeIII.PureDualTrace.quotient_eq_star
#print axioms PrimeGap182.TypeIII.PureDualTrace.dual_trace
#print axioms PrimeGap182.TypeIII.PureDualTrace.torusGeometryRules
