import TypeIIIPointImagePurity
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Relative image weights from compact weights and the same duality

Weil II 3.3.1 and 3.3.10 supply the general upper weight bound for R¹f!.
Apply it to the input and its dual. The existing guarded relative duality
and actual dual/Tate spectrum give the opposite bound on the ordinary
cohomology. The original image is a quotient of compact cohomology and
a subobject of ordinary cohomology. All spectral transports below are
proved for the original Frobenius, without semisimplicity or an ordinary
base-change premise. Frobenius automorphisms remain a general Weil input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.ImageWeightsFromCompact
open SourceInverseImageSystem RationalPointStalks PublishedPhysicalConstruction
open PointImagePurity OrdinaryBaseChangeFromDuality

universe u v mu h

section Linear
variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
  (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) (q : V →ₗ[ℂ] W)

theorem mem_roots_iff_not_injective (z : ℂ) :
    z ∈ f.charpoly.roots ↔ ¬ Function.Injective ⇑(f - z • (1 : V →ₗ[ℂ] V)) := by
  rw [Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Module.End.hasEigenvalue_iff, Module.End.eigenspace_def]
  exact not_congr LinearMap.ker_eq_bot

/-- An equivariant injection preserves membership in the characteristic roots. -/
theorem roots_of_injective (hq : Function.Injective q)
    (he : ∀ v, q (f v) = g (q v)) {z : ℂ} (hz : z ∈ f.charpoly.roots) :
    z ∈ g.charpoly.roots := by
  rw [mem_roots_iff_not_injective] at hz ⊢
  intro hg
  apply hz
  intro x y hxy
  apply hq
  apply hg
  have h := congrArg q hxy
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_sub, map_smul, he] using h

/-- For a quotient, use surjectivity of the shifted endomorphism on the
finite-dimensional source. No lifting of individual eigenvectors is assumed. -/
theorem roots_of_surjective (hq : Function.Surjective q)
    (he : ∀ v, q (f v) = g (q v)) {z : ℂ} (hz : z ∈ g.charpoly.roots) :
    z ∈ f.charpoly.roots := by
  rw [mem_roots_iff_not_injective] at hz ⊢
  intro hf
  apply hz
  apply LinearMap.injective_iff_surjective.mpr
  intro w
  obtain ⟨v, rfl⟩ := hq w
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.mp hf v
  refine ⟨q u, ?_⟩
  have h := congrArg q hu
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_sub, map_smul, he] using h

theorem root_ne_zero (hf : Function.Injective f) {z : ℂ} (hz : z ∈ f.charpoly.roots) :
    z ≠ 0 := by
  intro h
  subst z
  rw [mem_roots_iff_not_injective] at hz
  apply hz
  simpa only [zero_smul, sub_zero] using hf

end Linear

variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)} (R : Data B)

/-- Geometric Frobenius acts invertibly on each actual Weil stalk. -/
structure Automorphisms : Prop where
  isIso : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x A,
    IsIso ((R.frobenius E X x).app A)

theorem point_root_ne_zero (I : Automorphisms R)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X)
    {z : ℂ} (hz : z ∈ PureDualTrace.eigenvalues R E X x A) : z ≠ 0 := by
  let := R.finite E X x A
  let := I.isIso E X x A
  exact root_ne_zero ((R.frobenius E X x).app A).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) hz

theorem point_roots_mono (S : ExactStalks R)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X)
    {A C : B.Obj X} (f : A ⟶ C) [Mono f]
    {z : ℂ} (hz : z ∈ PureDualTrace.eigenvalues R E X x A) :
    z ∈ PureDualTrace.eigenvalues R E X x C := by
  let := S.limits E X x
  let := R.finite E X x A
  let := R.finite E X x C
  apply roots_of_injective ((R.frobenius E X x).app A).hom
    ((R.frobenius E X x).app C).hom ((R.fiber E X x).map f).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) _ hz
  intro v
  exact (congrArg (fun m => m.hom v) ((R.frobenius E X x).naturality f)).symm

theorem point_roots_epi (S : ExactStalks R)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X)
    {A C : B.Obj X} (f : A ⟶ C) [Epi f]
    {z : ℂ} (hz : z ∈ PureDualTrace.eigenvalues R E X x C) :
    z ∈ PureDualTrace.eigenvalues R E X x A := by
  let := S.colimits E X x
  let := R.finite E X x A
  let := R.finite E X x C
  apply roots_of_surjective ((R.frobenius E X x).app A).hom
    ((R.frobenius E X x).app C).hom ((R.fiber E X x).map f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) _ hz
  intro v
  exact (congrArg (fun m => m.hom v) ((R.frobenius E X x).naturality f)).symm

/-- Inversion and twist (-1) turn the dual compact upper bound into the
ordinary lower bound. Invertibility is essential when dividing. -/
theorem dual_weight_lower {q : ℝ} (hq : 0 < q) (a : ℝ) {t : ℂ} (ht : t ≠ 0)
    (hw : Complex.normSq t ≤ q ^ (-a + 1)) :
    q ^ (a + 1) ≤ Complex.normSq ((q : ℂ) / t) := by
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  apply (le_div_iff₀ (Complex.normSq_pos.mpr ht)).mpr
  calc
    q ^ (a + 1) * Complex.normSq t ≤ q ^ (a + 1) * q ^ (-a + 1) :=
      mul_le_mul_of_nonneg_left hw (le_of_lt (Real.rpow_pos_of_pos hq _))
    _ = q * q := by
      rw [← Real.rpow_add hq]
      have h : (a + 1) + (-a + 1) = (2 : ℝ) := by ring
      rw [h, Real.rpow_two]
      ring

variable {Point : Type h} (D : CurveData (B.Obj .source) Point)
  (H : CohomologyData (B.Obj .source) (B.Obj .torus))

/-- Degree-one case of the general compact direct-image weight theorem,
before choosing a Type III source or imposing slope/lissity conditions. -/
structure CompactUpperWeights : Prop where
  bound : ∀ A a, D.Pure A a →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
      (x : Spec (.of E) ⟶ scheme (ZMod p) .torus),
      ∀ z ∈ PureDualTrace.eigenvalues R E .torus x (H.compact A),
        Complex.normSq z ≤ (Fintype.card E : ℝ) ^ (a + 1)

variable {R D H} {P : ParameterData (B.Obj .torus)}
  {DT : (B.Obj .torus)ᵒᵖ ⥤ B.Obj .torus}

/-- The original core is a compact quotient and an ordinary subobject.
The existing relative duality supplies the lower bound on that same stalk. -/
theorem core_weight (S : ExactStalks R) (I : Automorphisms R)
    (W : CompactUpperWeights R D H) (CR : CurveRules D)
    (RD : RelativeDuality D (H := H) (P := P) DT)
    (DS : PureDualTrace.DualSpectrum R .torus DT P.Lisse 1)
    (A : B.Obj .source) (a : ℝ) (hl : D.Lisse A) (hp : D.Pure A a)
    (hd : D.Isoclinic (D.dual A) 1) (hcd : P.Lisse (H.compact (D.dual A)))
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) .torus)
    {z : ℂ} (hz : z ∈ PureDualTrace.eigenvalues R E .torus x (parabolicCore H A)) :
    Complex.normSq z = (Fintype.card E : ℝ) ^ (a + 1) := by
  have hcompact := point_roots_epi R S E .torus x (Abelian.factorThruImage (H.comparison A)) hz
  have hupper := W.bound A a hp E x z hcompact
  have hord := point_roots_mono R S E .torus x (Abelian.image.ι (H.comparison A)) hz
  have hdual := point_roots_mono R S E .torus x (RD.duality A hl hd hcd).hom hord
  rw [DS.roots E x (H.compact (D.dual A)) hcd] at hdual
  obtain ⟨t, ht, he⟩ := Multiset.mem_map.mp hdual
  have hw := W.bound (D.dual A) (-a) (CR.dual_pure A a hl hp) E x t ht
  have hn := point_root_ne_zero R I E .torus x (H.compact (D.dual A)) ht
  have hq : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  apply le_antisymm hupper
  rw [← he]
  simpa only [pow_one, Complex.ofReal_natCast] using dual_weight_lower hq a hn hw

/-- Discharge the former relative image-weight input by compact weights
and the pre-existing guarded relative duality on the same functors. -/
theorem imageWeights (S : ExactStalks R) (I : Automorphisms R)
    (W : CompactUpperWeights R D H) (CR : CurveRules D)
    (RD : RelativeDuality D (H := H) (P := P) DT)
    (DS : PureDualTrace.DualSpectrum R .torus DT P.Lisse 1) : ImageWeights R D H P where
  weight A a hl hp _ hd _ hcd E _ _ _ x z hz := by
    have hz' : z ∈ PureDualTrace.eigenvalues R E .torus x (parabolicCore H A) := by
      rw [show parabolicCore H A = Abelian.image (H.comparison A) from rfl,
        image_eigenvalues R S]
      exact hz
    exact core_weight S I W CR RD DS A a hl hp hd hcd E x hz'

end PrimeGap182.TypeIII.ImageWeightsFromCompact

#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.mem_roots_iff_not_injective
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.roots_of_injective
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.roots_of_surjective
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.root_ne_zero
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.point_root_ne_zero
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.point_roots_mono
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.point_roots_epi
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.dual_weight_lower
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.core_weight
#print axioms PrimeGap182.TypeIII.ImageWeightsFromCompact.imageWeights
