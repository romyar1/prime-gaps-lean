import TypeIIIAlgebraicDescent

/-!
# The actual coefficient action on Laurent Artin–Schreier classes

Coefficient automorphisms are lifted to the completed Laurent-series field,
then descended to its additive Artin–Schreier quotient. The resulting action
and pole-one equivariance are proved, not supplied as hypotheses. This file
does not identify these classes with the wild characters of an ℓ-adic sheaf.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped Classical BigOperators

set_option maxHeartbeats 1000000

variable {L : Type*} [Field L]

/-- Apply the actual coefficient-field automorphism to every Laurent-series
coefficient, with its inverse providing the actual inverse on series. -/
def laurentCoefficientEquiv (σ : L ≃+* L) : LaurentSeries L ≃+* LaurentSeries L where
  toFun f := f.map σ
  invFun f := f.map σ.symm
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp
  map_add' f g := HahnSeries.map_add σ.toAddMonoidHom
  map_mul' f g := HahnSeries.map_mul σ.toRingHom.toNonUnitalRingHom

@[simp] theorem laurentCoefficientEquiv_coeff (σ : L ≃+* L) (f : LaurentSeries L)
    (n : ℤ) : (laurentCoefficientEquiv σ f).coeff n = σ (f.coeff n) := rfl

@[simp] theorem laurentCoefficientEquiv_refl (f : LaurentSeries L) :
    laurentCoefficientEquiv (RingEquiv.refl L) f = f := by
  ext n
  rfl

theorem laurentCoefficientEquiv_trans (σ τ : L ≃+* L) (f : LaurentSeries L) :
    laurentCoefficientEquiv (σ.trans τ) f =
      laurentCoefficientEquiv τ (laurentCoefficientEquiv σ f) := by
  ext n
  rfl

@[simp] theorem laurentCoefficientEquiv_poleOne (σ : L ≃+* L) (c : L) :
    laurentCoefficientEquiv σ (laurentPoleOne c) = laurentPoleOne (σ c) := by
  simp only [laurentPoleOne_eq_single]
  ext n
  by_cases hn : n = -1 <;> simp [hn]

section PrimeCharacteristic

variable (p : ℕ) [Fact p.Prime] [CharP L p]

/-- The actual additive quotient of the complete Laurent-series field. -/
abbrev laurentArtinSchreierQuotient :=
  LaurentSeries L ⧸ (laurentArtinSchreierMap (k := L) p).range

theorem laurentCoefficientEquiv_artinSchreier (σ : L ≃+* L) (f : LaurentSeries L) :
    laurentCoefficientEquiv σ (laurentArtinSchreierMap p f) =
      laurentArtinSchreierMap p (laurentCoefficientEquiv σ f) := by
  simp only [laurentArtinSchreierMap_apply, map_sub, map_pow]

/-- The image of Frobenius minus identity is preserved onto itself. -/
theorem laurentArtinSchreierRange_map (σ : L ≃+* L) :
    (laurentArtinSchreierMap (k := L) p).range.map
      (laurentCoefficientEquiv σ).toAddMonoidHom =
      (laurentArtinSchreierMap (k := L) p).range := by
  apply le_antisymm
  · rintro f ⟨g, ⟨h, rfl⟩, rfl⟩
    exact ⟨laurentCoefficientEquiv σ h,
      (laurentCoefficientEquiv_artinSchreier p σ h).symm⟩
  · rintro f ⟨g, rfl⟩
    refine ⟨laurentArtinSchreierMap p ((laurentCoefficientEquiv σ).symm g),
      ⟨(laurentCoefficientEquiv σ).symm g, rfl⟩, ?_⟩
    change laurentCoefficientEquiv σ
      (laurentArtinSchreierMap p ((laurentCoefficientEquiv σ).symm g)) =
        laurentArtinSchreierMap p g
    rw [laurentCoefficientEquiv_artinSchreier, RingEquiv.apply_symm_apply]

/-- The additive equivalence on the full Artin–Schreier quotient induced by
the actual Laurent-series automorphism. -/
def laurentArtinSchreierEquiv (σ : L ≃+* L) :
    laurentArtinSchreierQuotient (L := L) p ≃+
      laurentArtinSchreierQuotient (L := L) p :=
  QuotientAddGroup.congr _ _ (laurentCoefficientEquiv σ).toAddEquiv
    (laurentArtinSchreierRange_map p σ)

@[simp] theorem laurentArtinSchreierEquiv_mk (σ : L ≃+* L) (f : LaurentSeries L) :
    laurentArtinSchreierEquiv p σ (QuotientAddGroup.mk f) =
      QuotientAddGroup.mk (laurentCoefficientEquiv σ f) := rfl

@[simp] theorem laurentArtinSchreierEquiv_poleOneClass (σ : L ≃+* L) (c : L) :
    laurentArtinSchreierEquiv p σ (laurentPoleOneClass p c) =
      laurentPoleOneClass p (σ c) := by
  simp only [laurentPoleOneClass, laurentArtinSchreierEquiv_mk,
    laurentCoefficientEquiv_poleOne]

@[simp] theorem laurentArtinSchreierEquiv_refl
    (q : laurentArtinSchreierQuotient (L := L) p) :
    laurentArtinSchreierEquiv p (RingEquiv.refl L) q = q := by
  induction q using QuotientAddGroup.induction_on with
  | H f => simp only [laurentArtinSchreierEquiv_mk, laurentCoefficientEquiv_refl]

theorem laurentArtinSchreierEquiv_trans (σ τ : L ≃+* L)
    (q : laurentArtinSchreierQuotient (L := L) p) :
    laurentArtinSchreierEquiv p (σ.trans τ) q =
      laurentArtinSchreierEquiv p τ (laurentArtinSchreierEquiv p σ q) := by
  induction q using QuotientAddGroup.induction_on with
  | H f => simp only [laurentArtinSchreierEquiv_mk, laurentCoefficientEquiv_trans]

variable {k : Type*} [Field k] [Algebra k L]

theorem laurentArtinSchreierEquiv_one
    (q : laurentArtinSchreierQuotient (L := L) p) :
    laurentArtinSchreierEquiv p (1 : L ≃ₐ[k] L).toRingEquiv q = q :=
  laurentArtinSchreierEquiv_refl p q

theorem laurentArtinSchreierEquiv_mul (σ τ : L ≃ₐ[k] L)
    (q : laurentArtinSchreierQuotient (L := L) p) :
    laurentArtinSchreierEquiv p (σ * τ).toRingEquiv q =
      laurentArtinSchreierEquiv p σ.toRingEquiv
        (laurentArtinSchreierEquiv p τ.toRingEquiv q) :=
  laurentArtinSchreierEquiv_trans p τ.toRingEquiv σ.toRingEquiv q

/-- A genuine distributive group action of the constant-field automorphisms
on the whole additive quotient; no action law is assumed. -/
@[instance_reducible] def laurentArtinSchreierAction :
    DistribMulAction (L ≃ₐ[k] L) (laurentArtinSchreierQuotient (L := L) p) where
  smul σ q := laurentArtinSchreierEquiv p σ.toRingEquiv q
  one_smul := laurentArtinSchreierEquiv_one p
  mul_smul := laurentArtinSchreierEquiv_mul p
  smul_zero σ := (laurentArtinSchreierEquiv p σ.toRingEquiv).map_zero
  smul_add σ a b := (laurentArtinSchreierEquiv p σ.toRingEquiv).map_add a b

theorem laurentArtinSchreierAction_poleOneClass (σ : L ≃ₐ[k] L) (x : L) :
    letI := laurentArtinSchreierAction (k := k) (L := L) p
    σ • laurentPoleOneClass p x = laurentPoleOneClass p (σ x) :=
  laurentArtinSchreierEquiv_poleOneClass p σ.toRingEquiv x

/-- A finite invariant set in the actual quotient gives a finite orbit of
any pole-one coefficient represented in that set. The passage back to
coefficients uses the proved pole-one class injectivity. -/
theorem finite_coefficient_orbit_of_finite_invariant_artinSchreier_set
    (S : Set (laurentArtinSchreierQuotient (L := L) p)) (hS : S.Finite)
    (hstable : ∀ σ : L ≃ₐ[k] L, ∀ q ∈ S,
      laurentArtinSchreierEquiv p σ.toRingEquiv q ∈ S)
    (x : L) (hx : laurentPoleOneClass p x ∈ S) :
    (Set.range (fun σ : L ≃ₐ[k] L => σ x)).Finite := by
  have hclasses : (Set.range ((laurentPoleOneClass p) ∘
      (fun σ : L ≃ₐ[k] L => σ x))).Finite := by
    apply hS.subset
    rintro _ ⟨σ, rfl⟩
    change laurentPoleOneClass p (σ x) ∈ S
    have hσ := hstable σ _ hx
    rw [laurentArtinSchreierEquiv_poleOneClass] at hσ
    exact hσ
  rw [Set.range_comp,
    Set.finite_image_iff (laurentPoleOneClass_injective p).injOn] at hclasses
  exact hclasses

end PrimeCharacteristic

section RationalClosure

variable {k : Type*} [Field k] [IsAlgClosed k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- For the actual algebraic closure of `k(z)`, finite invariant quotient
class sets can contain a pole-one phase only with constant coefficient. -/
theorem constant_of_mem_finite_invariant_artinSchreier_set
    (S : Set (laurentArtinSchreierQuotient (L := AlgebraicClosure (RatFunc k)) p))
    (hS : S.Finite)
    (hstable : ∀ σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k), ∀ q ∈ S,
        laurentArtinSchreierEquiv p σ.toRingEquiv q ∈ S)
    (x : AlgebraicClosure (RatFunc k)) (hx : laurentPoleOneClass p x ∈ S) :
    ∃ c : k, algebraMap k (AlgebraicClosure (RatFunc k)) c = x := by
  apply (rationalAlgebraicClosure_finite_orbit_iff k x).mp
  exact finite_coefficient_orbit_of_finite_invariant_artinSchreier_set p S hS hstable x hx

/-- The rescaled distinct-rectangle phases cannot belong to any finite set
stable under the actual automorphism action on Artin–Schreier classes. This
uses the already proved scalar phase obstruction and actual infinite orbit. -/
theorem rescaled_distinctRectanglePhase_not_mem_finite_invariant_artinSchreier_set
    (h2 : (2 : k) ≠ 0) (α : k) (hα : α ≠ 0) (m n : Fin 2 → k)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0)
    (hminj : Function.Injective m) (hninj : Function.Injective n)
    (s : Finset PhaseRectangle) (hs : s.Nonempty) (γ A : PhaseRectangle → k)
    (hγ : ∀ e ∈ s, γ e ^ 3 = m e.1 / n e.2)
    (hA : ∀ e ∈ s, A e ^ 2 = 4 * α / m e.1)
    (R : PhaseRectangle → AlgebraicClosure (RatFunc k))
    (hR : ∀ e ∈ s, R e ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C (γ e) - RatFunc.X))
    (a b : k) (u : AlgebraicClosure (RatFunc k)) (hu0 : u ≠ 0)
    (hu : u ^ 2 = algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))
      (RatFunc.C a + RatFunc.C b * RatFunc.X))
    (S : Set (laurentArtinSchreierQuotient (L := AlgebraicClosure (RatFunc k)) p))
    (hS : S.Finite)
    (hstable : ∀ σ : AlgebraicClosure (RatFunc k) ≃ₐ[k]
      AlgebraicClosure (RatFunc k), ∀ q ∈ S,
        laurentArtinSchreierEquiv p σ.toRingEquiv q ∈ S) :
    laurentPoleOneClass p ((∑ e ∈ s, radialPhaseScalar (A e) (γ e) • R e) * u) ∉ S := by
  intro hmem
  exact (rescaled_distinctRectanglePhase_infinite_orbit h2 α hα m n hm hn hminj hninj
    s hs γ A hγ hA R hR a b u hu0 hu)
      (finite_coefficient_orbit_of_finite_invariant_artinSchreier_set p S hS hstable _ hmem)

end RationalClosure

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.laurentArtinSchreierRange_map
#print axioms PrimeGap182.TypeIII.laurentArtinSchreierEquiv_poleOneClass
#print axioms PrimeGap182.TypeIII.laurentArtinSchreierAction
#print axioms PrimeGap182.TypeIII.laurentArtinSchreierAction_poleOneClass
#print axioms PrimeGap182.TypeIII.finite_coefficient_orbit_of_finite_invariant_artinSchreier_set
#print axioms PrimeGap182.TypeIII.constant_of_mem_finite_invariant_artinSchreier_set
#print axioms PrimeGap182.TypeIII.rescaled_distinctRectanglePhase_not_mem_finite_invariant_artinSchreier_set
