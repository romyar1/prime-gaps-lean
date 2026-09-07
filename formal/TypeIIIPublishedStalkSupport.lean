import TypeIIIPublishedSupportRules
import TypeIIIUniformStalkCriterion

/-!
# From conditional geometric support rules to the original stalk certificates

The point map in this file is the actual coefficient inclusion from `ZMod p`
to its algebraic closure. Its injectivity proves that restricting a finite
geometric exceptional set cannot increase cardinality. Polynomial supports
are evaluated by the original `planeEval`.

The two adapters return the original `TypeIIIFiniteStalkSupport` and
`TypeIIICurveStalkSupport` records for the same spectra already present in
a `TypeIIIStalkCertificate`. Equality with the chosen rational realization
is an explicit input. The finite branch uses the generic BBD/QST rules and
full support of the chosen objects' simple constituents. The curve branch
uses the generic ordinary-support degree rule and a separately supplied
coefficient/dilation isomorphism; a uniform constituent bound and prime
cutoff then place ordinary degree zero at the origin.

This is a conditional adapter. It supplies no sheaf realization, family
covariance, constituent exclusion, trace formula, or Fourier estimate. The
numerical support bounds and cutoff are explicit so a uniform application
can fix them before choosing its prime and residue parameters.
-/

noncomputable section
open scoped Classical

namespace PrimeGap182.TypeIII.PublishedStalkSupport

open PublishedSupportRules

universe u

/-- The actual inclusion of prime-field frequency pairs into the geometric
plane over the algebraic closure. -/
def primeFieldPoint (p : ℕ) [Fact p.Prime] (z : ZMod p × ZMod p) :
    AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p) :=
  (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) z.1,
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) z.2)

theorem primeFieldPoint_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (primeFieldPoint p) := by
  intro z w h
  apply Prod.ext
  · exact (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
      (congrArg Prod.fst h)
  · exact (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
      (congrArg Prod.snd h)

@[simp] theorem primeFieldPoint_zero (p : ℕ) [Fact p.Prime] :
    primeFieldPoint p (0, 0) = (0, 0) := by
  simp [primeFieldPoint]

theorem primeFieldPoint_eq_zero_iff (p : ℕ) [Fact p.Prime]
    (z : ZMod p × ZMod p) :
    primeFieldPoint p z = (0, 0) ↔ z = (0, 0) := by
  rw [← primeFieldPoint_zero p]
  exact (primeFieldPoint_injective p).eq_iff

/-- Literal preimage, written as a filter on the finite prime-field plane. -/
def primeFieldPreimage (p : ℕ) [Fact p.Prime]
    (Z : Finset (AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))) :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun z => primeFieldPoint p z ∈ Z

@[simp] theorem mem_primeFieldPreimage (p : ℕ) [Fact p.Prime]
    (Z : Finset (AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p)))
    (z : ZMod p × ZMod p) :
    z ∈ primeFieldPreimage p Z ↔ primeFieldPoint p z ∈ Z := by
  simp [primeFieldPreimage]

/-- Cardinality control comes from the actual injective coefficient map;
there is no assumption that all geometric exceptional points are rational. -/
theorem primeFieldPreimage_card_le (p : ℕ) [Fact p.Prime]
    (Z : Finset (AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p))) :
    (primeFieldPreimage p Z).card ≤ Z.card := by
  calc
    _ = ((primeFieldPreimage p Z).image (primeFieldPoint p)).card :=
      (Finset.card_image_of_injective _ (primeFieldPoint_injective p)).symm
    _ ≤ _ := Finset.card_le_card (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact (mem_primeFieldPreimage p Z w).mp hw)

/-- The polynomial evaluation used by the original Type III certificate
is evaluation at this same coefficient inclusion. -/
theorem planeEval_eq_geometric_eval (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) (h k : ZMod p) :
    planeEval p F h k =
      MvPolynomial.eval ![(primeFieldPoint p (h, k)).1,
        (primeFieldPoint p (h, k)).2] F := rfl

variable {p : ℕ} [Fact p.Prime] {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}

/-- A single-object finite-support consequence. The same lemma can be
used for physical spectra when a separate realization is supplied. -/
theorem exists_finite_rational_support (bbd : BBDRules D) (qst : QSTRules D)
    (realization : RationalStalkRealization p D) (Q : Obj)
    (W : realization.WeilLift Q) (hQ : D.Pure Q)
    (hfull : D.NoProperConstituents Q) :
    ∃ Z : Finset (ZMod p × ZMod p),
      Z.card ≤ qst.ordinarySupportBound (D.complexity Q) ∧
      (∀ h k, (h, k) ∉ Z → (realization.stalk W h k).minusOne.dimension = 0) ∧
      (∀ h k, (realization.stalk W h k).zero.dimension = 0) := by
  obtain ⟨Z, hcard, _, hminus, hzero⟩ :=
    exists_bounded_minusOne_support_of_no_proper_constituents bbd qst Q hQ hfull
  refine ⟨primeFieldPreimage p Z,
    (primeFieldPreimage_card_le p Z).trans hcard, ?_, ?_⟩
  · intro h k hz
    rw [realization.minusOne_dimension W h k]
    exact hminus (primeFieldPoint p (h, k))
      (fun hmem => hz ((mem_primeFieldPreimage p Z (h, k)).mpr hmem))
  · intro h k
    rw [realization.zero_dimension W h k]
    exact hzero (primeFieldPoint p (h, k))

/-- An origin-only geometric degree-zero support yields the corresponding
vanishing at every nonzero rational frequency. -/
theorem rational_zero_dimension_of_origin_support
    (realization : RationalStalkRealization p D) (Q : Obj)
    (W : realization.WeilLift Q)
    (hsupport : D.ordinarySupport Q 2 ⊆ {(0, 0)})
    (h k : ZMod p) (hne : ¬ (h = 0 ∧ k = 0)) :
    (realization.stalk W h k).zero.dimension = 0 := by
  rw [realization.zero_dimension W h k]
  by_contra hdim
  have hzero : primeFieldPoint p (h, k) = (0, 0) := hsupport hdim
  have hpair := (primeFieldPoint_eq_zero_iff p (h, k)).mp hzero
  exact hne (Prod.mk.inj hpair)

/-- The original geometric polynomial gives an actual `planeEval` support
condition for the rational degree-minus-one Frobenius block. -/
theorem exists_curve_rational_minusOne_support (degrees : OrdinarySupportDegreeRules D)
    (realization : RationalStalkRealization p D) (Q : Obj)
    (W : realization.WeilLift Q) :
    ∃ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)),
      F ≠ 0 ∧ F.totalDegree ≤ degrees.degreeBound (D.complexity Q) ∧
      ∀ h k, planeEval p F h k ≠ 0 →
        (realization.stalk W h k).minusOne.dimension = 0 := by
  obtain ⟨F, hF, hdegree, hvan⟩ := degrees.minusOne_polynomial Q
  refine ⟨F, hF, hdegree, ?_⟩
  intro h k hnonzero
  rw [realization.minusOne_dimension W h k]
  by_contra hdim
  exact hnonzero (hvan (primeFieldPoint p (h, k)) hdim)

/-- The distinct-index support adapter. All family-specific inputs remain
visible: purity, full support, and equality with the original spectra. -/
def finiteSupport {B Dphys Rphys Dcore : ℕ} {α m m' n n' : ZMod p}
    (certificate : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n')
    (D : SurfaceData (AlgebraicClosure (ZMod p)) Obj)
    (bbd : BBDRules D) (qst : QSTRules D)
    (realization : RationalStalkRealization p D)
    (objects : Finset (Fin 4) → Obj)
    (lifts : ∀ S, realization.WeilLift (objects S))
    (hreal : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      certificate.transformed S h k = realization.stalk (lifts S) h k)
    (hpure : ∀ S ∈ nonemptyCoreSubsets, D.Pure (objects S))
    (hfull : ∀ S ∈ nonemptyCoreSubsets, D.NoProperConstituents (objects S))
    (hbound : ∀ S ∈ nonemptyCoreSubsets,
      qst.ordinarySupportBound (D.complexity (objects S)) ≤ Dcore) :
    TypeIIIFiniteStalkSupport certificate Dcore := by
  have hexists : ∀ S : Finset (Fin 4), ∃ Z : Finset (ZMod p × ZMod p),
      ∀ hS : S ∈ nonemptyCoreSubsets,
        Z.card ≤ Dcore ∧
        (∀ h k, (h, k) ∉ Z →
          (realization.stalk (lifts S) h k).minusOne.dimension = 0) ∧
        (∀ h k, (realization.stalk (lifts S) h k).zero.dimension = 0) := by
    intro S
    by_cases hS : S ∈ nonemptyCoreSubsets
    · obtain ⟨Z, hcard, hminus, hzero⟩ := exists_finite_rational_support bbd qst
        realization (objects S) (lifts S) (hpure S hS) (hfull S hS)
      exact ⟨Z, fun _ => ⟨hcard.trans (hbound S hS), hminus, hzero⟩⟩
    · exact ⟨∅, fun h => (hS h).elim⟩
  choose exceptional hexceptional using hexists
  refine {
    exceptional := exceptional
    exceptional_card := fun S hS => (hexceptional S hS).1
    minusOne := ?_
    zero := ?_ }
  · intro S hS h k hnot
    rw [hreal S hS h k]
    exact (hexceptional S hS).2.1 h k hnot
  · intro S hS h k
    rw [hreal S hS h k]
    exact (hexceptional S hS).2.2 h k

/-- The repeated-index support adapter. `Npunct` and `p₀` are supplied
uniform constants, and the cutoff follows from `8^Npunct ≤ p₀ < p`.
Curve support is allowed; no full-support hypothesis is used. -/
def curveSupport {B Dphys Rphys Dcore : ℕ} {α m m' n n' : ZMod p}
    (certificate : TypeIIIStalkCertificate p B Dphys Rphys α m m' n n')
    (D : SurfaceData (AlgebraicClosure (ZMod p)) Obj)
    (bbd : BBDRules D) (qst : QSTRules D)
    (degrees : OrdinarySupportDegreeRules D) (transport : CoefficientTransport D)
    (realization : RationalStalkRealization p D)
    (objects : Finset (Fin 4) → Obj)
    (lifts : ∀ S, realization.WeilLift (objects S))
    (a : (AlgebraicClosure (ZMod p))ˣ) (ha : (a : AlgebraicClosure (ZMod p)) = 8)
    (Npunct p₀ : ℕ) (hcutoff : 8 ^ Npunct ≤ p₀) (hp : p₀ < p)
    (hreal : ∀ S ∈ nonemptyCoreSubsets, ∀ h k,
      certificate.transformed S h k = realization.stalk (lifts S) h k)
    (hpure : ∀ S ∈ nonemptyCoreSubsets, D.Pure (objects S))
    (hcov : ∀ S ∈ nonemptyCoreSubsets,
      transport.Isomorphic (transport.coefficient (objects S))
        (transport.dilate a (objects S)))
    (hdegree : ∀ S ∈ nonemptyCoreSubsets,
      degrees.degreeBound (D.complexity (objects S)) ≤ Dcore)
    (hpunct : ∀ S ∈ nonemptyCoreSubsets,
      qst.constituentBound (D.complexity (objects S)) ≤ Npunct) :
    TypeIIICurveStalkSupport certificate Dcore := by
  choose equation hequation using
    fun S => exists_curve_rational_minusOne_support degrees realization (objects S) (lifts S)
  refine {
    equation := equation
    equation_ne_zero := fun S _ => (hequation S).1
    equation_degree := fun S hS => (hequation S).2.1.trans (hdegree S hS)
    minusOne := ?_
    zero := ?_ }
  · intro S hS h k hnonzero
    rw [hreal S hS h k]
    exact (hequation S).2.2 h k hnonzero
  · intro S hS h k hne
    rw [hreal S hS h k]
    apply rational_zero_dimension_of_origin_support realization (objects S) (lifts S) _ h k hne
    apply zero_support_subset_origin_of_covariance bbd qst transport
      (objects S) (hpure S hS) a ha (hcov S hS)
    exact (Nat.pow_le_pow_right (by decide : 0 < 8) (hpunct S hS)).trans_lt
      (hcutoff.trans_lt hp)

#print axioms primeFieldPoint
#print axioms primeFieldPoint_injective
#print axioms primeFieldPoint_zero
#print axioms primeFieldPoint_eq_zero_iff
#print axioms primeFieldPreimage
#print axioms mem_primeFieldPreimage
#print axioms primeFieldPreimage_card_le
#print axioms planeEval_eq_geometric_eval
#print axioms exists_finite_rational_support
#print axioms rational_zero_dimension_of_origin_support
#print axioms exists_curve_rational_minusOne_support
#print axioms finiteSupport
#print axioms curveSupport

end PrimeGap182.TypeIII.PublishedStalkSupport
