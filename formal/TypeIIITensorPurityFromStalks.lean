import TypeIIIParameterPurityFromStalks

/-!
# Tensor purity from the original Frobenius operators

The eigenvalues of a tensor product are products of eigenvalues of its
factors. Prove the needed membership statement using eigenspaces of
commuting operators and invertibility of scalar shifts. No diagonalizable
or semisimple Frobenius premise is needed. Apply this to the existing
monoidal stalk comparison at every actual finite-field scheme point.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct

namespace PrimeGap182.TypeIII.TensorPurityFromStalks
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- An eigenvalue of a product of commuting endomorphisms is a product
of eigenvalues, without assuming either endomorphism is semisimple. -/
theorem roots_mul (f g : V →ₗ[ℂ] V) (hc : Commute f g) {z : ℂ}
    (hz : z ∈ (f * g).charpoly.roots) :
    ∃ a ∈ f.charpoly.roots, ∃ b ∈ g.charpoly.roots, z = a * b := by
  have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly (f * g) z).mpr
    ((Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hz)
  let S := Module.End.eigenspace (f * g) z
  let : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr
    ((Module.End.hasEigenvalue_iff).mp he)
  have hfg (x : V) : f (g x) = g (f x) := congrArg (fun m : V →ₗ[ℂ] V => m x) hc.eq
  have hfS : ∀ x ∈ S, f x ∈ S := by
    intro x hx
    apply Module.End.mem_eigenspace_iff.mpr
    have hx' : f (g x) = z • x := Module.End.mem_eigenspace_iff.mp hx
    change f (g (f x)) = z • f x
    rw [← hfg x, hx', map_smul]
  have hgS : ∀ x ∈ S, g x ∈ S := by
    intro x hx
    apply Module.End.mem_eigenspace_iff.mpr
    have hx' : f (g x) = z • x := Module.End.mem_eigenspace_iff.mp hx
    change f (g (g x)) = z • g x
    rw [hfg (g x), hx', map_smul]
  let fs : S →ₗ[ℂ] S := f.restrict hfS
  let gs : S →ₗ[ℂ] S := g.restrict hgS
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue fs
  let T := Module.End.eigenspace fs a
  let : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr
    ((Module.End.hasEigenvalue_iff).mp ha)
  have hgs : ∀ x ∈ T, gs x ∈ T := by
    intro x hx
    apply Module.End.mem_eigenspace_iff.mpr
    apply Subtype.ext
    have hx' : f (x : V) = a • (x : V) :=
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hx)
    change f (g (x : V)) = a • g (x : V)
    rw [hfg, hx', map_smul]
  obtain ⟨b, hb⟩ := Module.End.exists_eigenvalue (gs.restrict hgs)
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  let w : V := ((v : T) : S)
  have hw : w ≠ 0 := by
    intro h
    exact (Module.End.hasEigenvector_iff.mp hv).2 (Subtype.ext (Subtype.ext h))
  have hf : f w = a • w :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp v.property)
  have hg : g w = b • w :=
    congrArg (fun t : T => ((t : T) : S).val) hv.apply_eq_smul
  have hz' : f (g w) = z • w := Module.End.mem_eigenspace_iff.mp (v : S).property
  have hroot (k : V →ₗ[ℂ] V) (c : ℂ) (h : k w = c • w) : c ∈ k.charpoly.roots := by
    apply (Polynomial.mem_roots (LinearMap.charpoly_monic k).ne_zero).mpr
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly k c).mp
    apply Module.End.hasEigenvalue_iff.mpr
    intro hbot
    have hm : w ∈ Module.End.eigenspace k c := Module.End.mem_eigenspace_iff.mpr h
    rw [hbot, Submodule.mem_bot] at hm
    exact hw hm
  refine ⟨a, hroot f a hf, b, hroot g b hg, ?_⟩
  have hs : (z - a * b) • w = 0 := by
    rw [sub_smul, mul_comm a b, mul_smul, ← hf, ← map_smul, ← hg, hz', sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hw)

variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Tensoring with identity cannot introduce new characteristic roots. -/
theorem roots_tensor_left (f : V →ₗ[ℂ] V) {z : ℂ}
    (hz : z ∈ (TensorProduct.map f (1 : W →ₗ[ℂ] W)).charpoly.roots) :
    z ∈ f.charpoly.roots := by
  classical
  by_contra h
  have hf : Function.Injective ⇑(f - z • (1 : V →ₗ[ℂ] V)) := by
    by_contra hi
    exact h ((ImageWeightsFromCompact.mem_roots_iff_not_injective f z).mpr hi)
  have hb := TensorProduct.map_bijective ⟨hf, LinearMap.injective_iff_surjective.mp hf⟩
    (show Function.Bijective ⇑(1 : W →ₗ[ℂ] W) from Function.bijective_id)
  have he : TensorProduct.map (f - z • (1 : V →ₗ[ℂ] V)) (1 : W →ₗ[ℂ] W) =
      TensorProduct.map f (1 : W →ₗ[ℂ] W) - z • (1 : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) := by
    ext x y
    change (f x - z • x) ⊗ₜ[ℂ] y = f x ⊗ₜ[ℂ] y - z • (x ⊗ₜ[ℂ] y)
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul']
  exact ((ImageWeightsFromCompact.mem_roots_iff_not_injective _ z).mp hz)
    (by rw [← he]; exact hb.1)

/-- The corresponding statement for tensoring identity with an operator. -/
theorem roots_tensor_right (g : W →ₗ[ℂ] W) {z : ℂ}
    (hz : z ∈ (TensorProduct.map (1 : V →ₗ[ℂ] V) g).charpoly.roots) :
    z ∈ g.charpoly.roots := by
  classical
  by_contra h
  have hg : Function.Injective ⇑(g - z • (1 : W →ₗ[ℂ] W)) := by
    by_contra hi
    exact h ((ImageWeightsFromCompact.mem_roots_iff_not_injective g z).mpr hi)
  have hb := TensorProduct.map_bijective
    (show Function.Bijective ⇑(1 : V →ₗ[ℂ] V) from Function.bijective_id)
    ⟨hg, LinearMap.injective_iff_surjective.mp hg⟩
  have he : TensorProduct.map (1 : V →ₗ[ℂ] V) (g - z • (1 : W →ₗ[ℂ] W)) =
      TensorProduct.map (1 : V →ₗ[ℂ] V) g - z • (1 : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) := by
    ext x y
    change x ⊗ₜ[ℂ] (g y - z • y) = x ⊗ₜ[ℂ] g y - z • (x ⊗ₜ[ℂ] y)
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  exact ((ImageWeightsFromCompact.mem_roots_iff_not_injective _ z).mp hz)
    (by rw [← he]; exact hb.1)

/-- All roots of a tensor operator are products of roots of its factors.
This includes zero-dimensional spaces and does not assume diagonalizability. -/
theorem roots_tensor (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) {z : ℂ}
    (hz : z ∈ (TensorProduct.map f g).charpoly.roots) :
    ∃ a ∈ f.charpoly.roots, ∃ b ∈ g.charpoly.roots, z = a * b := by
  let l := TensorProduct.map f (1 : W →ₗ[ℂ] W)
  let r := TensorProduct.map (1 : V →ₗ[ℂ] V) g
  have hc : Commute l r := by
    change l * r = r * l
    ext x y
    rfl
  have he : l * r = TensorProduct.map f g := by
    ext x y
    rfl
  obtain ⟨a, ha, b, hb, hab⟩ := roots_mul l r hc (he ▸ hz)
  exact ⟨a, roots_tensor_left f ha, b, roots_tensor_right g hb, hab⟩

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open SourceInverseImageSystem RationalPointStalks ParameterPurityFromStalks
open PublishedPhysicalConstruction

universe mu
variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)}
  (R : Data B) (T : PointTraceFromTensor.Laws R)

include T in
/-- The original monoidal stalk comparison and product eigenvalues imply
pointwise tensor purity at all actual finite-field scheme points. -/
theorem tensor_pure (X : Space (ZMod p)) (A C : B.Obj X) (a b : ℝ)
    (hA : pointwisePure R X A a) (hC : pointwisePure R X C b) :
    pointwisePure R X (A ⊗ C) (a + b) := by
  intro E _ _ _ x z hz
  let := R.finite E X x A
  let := R.finite E X x C
  let := R.finite E X x (A ⊗ C)
  let S := T.tensorRules E X x
  let e := S.comparison A C
  have h := ImageWeightsFromCompact.roots_of_injective
    ((R.frobenius E X x).app (A ⊗ C)).hom
    (TensorProduct.map ((R.frobenius E X x).app A).hom ((R.frobenius E X x).app C).hom)
    e.toLinearMap e.injective (S.frobenius A C) hz
  obtain ⟨u, hu, v, hv, rfl⟩ := roots_tensor _ _ h
  have hq : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Complex.normSq_mul, hA E x u hu, hC E x v hv, Real.rpow_add hq]

/-- Only the original lissity rules remain; tensor purity is derived. -/
structure TorusLissity (P : ParameterData (B.Obj .torus)) : Prop where
  pullback_lisse : ∀ f A, P.Lisse A → P.Lisse ((B.torusOperations.pullback f).obj A)
  unit_lisse : P.Lisse (𝟙_ (B.Obj .torus))
  tensor_lisse : ∀ A C, P.Lisse A → P.Lisse C → P.Lisse (A ⊗ C)

variable (L : B.Obj .torus → Prop) (line : B.Obj .torus)
  (dual : (B.Obj .torus)ᵒᵖ ⥤ B.Obj .torus)

include T in
/-- Supply the old torus interface using the checked tensor-weight argument. -/
theorem torusRules
    (G : TorusLissity (((parameterGeometry R L).withLine line).data dual)) :
    TorusRules (((parameterGeometry R L).withLine line).data dual) where
  pullback_lisse := G.pullback_lisse
  unit_lisse := G.unit_lisse
  tensor_lisse := G.tensor_lisse
  tensor_pure := tensor_pure R T .torus

end PrimeGap182.TypeIII.TensorPurityFromStalks

#print axioms PrimeGap182.TypeIII.TensorPurityFromStalks.roots_mul
#print axioms PrimeGap182.TypeIII.TensorPurityFromStalks.roots_tensor_left
#print axioms PrimeGap182.TypeIII.TensorPurityFromStalks.roots_tensor_right
#print axioms PrimeGap182.TypeIII.TensorPurityFromStalks.roots_tensor
#print axioms PrimeGap182.TypeIII.TensorPurityFromStalks.tensor_pure
#print axioms PrimeGap182.TypeIII.TensorPurityFromStalks.torusRules
