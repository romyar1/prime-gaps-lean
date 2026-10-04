import TypeIIIBoundaryFromSourceModels
import TypeIIITensorBoundaryFrobenius

/-!
# Frobenius through the actual source restriction comparisons

General tensor and dual naturality laws imply the Frobenius comparison
for the literal three-factor curve input. Individual source models then
carry its action to the same regular-unipotent tensor used in the boundary
calculation. No Frobenius law for the finished input is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical TensorProduct

namespace PrimeGap182.TypeIII.RestrictionFrobenius

open PublishedMackey PublishedPhaseApplication RegularUnipotentBoundary
open TensorBoundaryFrobenius

universe u v w z a b
variable {k : Type u} [Field k] {G : Type v} [Group G]

/-- Tensor comparison maps preserve any pair of compatible operators. -/
theorem tensorEquiv_natural {A B C D : FDRep k G}
    (f : Representation.Equiv A.ρ B.ρ) (g : Representation.Equiv C.ρ D.ρ)
    (s : Module.End k A.V) (t : Module.End k C.V)
    (s' : Module.End k B.V) (t' : Module.End k D.V)
    (hs : ∀ x, f (s x) = s' (f x)) (ht : ∀ x, g (t x) = t' (g x))
    (x : (tensor A C).V) :
    tensorEquiv f g (TensorProduct.map s t x) =
      TensorProduct.map s' t' (tensorEquiv f g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change f (s x) ⊗ₜ[k] g (t y) = s' (f x) ⊗ₜ[k] t' (g y)
    rw [hs, ht]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Compatibility with invertible operators also controls their inverses. -/
theorem inverse_natural {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : V ≃ₗ[k] W)
    (s : V ≃ₗ[k] V) (t : W ≃ₗ[k] W)
    (h : ∀ x, f (s x) = t (f x)) (x : V) :
    f (s.symm x) = t.symm (f x) := by
  apply t.injective
  rw [← h, s.apply_symm_apply, t.apply_symm_apply]

/-- The contragredient comparison uses the inverse source operator. -/
theorem dualEquiv_natural {A B : FDRep k G}
    (f : Representation.Equiv A.ρ B.ρ) (s : A.V ≃ₗ[k] A.V) (t : B.V ≃ₗ[k] B.V)
    (h : ∀ x, f (s x) = t (f x)) (phi : Module.Dual k A.V) :
    dualEquiv f (s.symm.toLinearMap.dualMap phi) =
      t.symm.toLinearMap.dualMap (dualEquiv f phi) := by
  apply LinearMap.ext
  intro y
  change phi (s.symm (f.toLinearEquiv.symm y)) = phi (f.toLinearEquiv.symm (t.symm y))
  congr 1
  apply f.toLinearEquiv.injective
  rw [inverse_natural f.toLinearEquiv s t h,
    f.toLinearEquiv.apply_symm_apply, f.toLinearEquiv.apply_symm_apply]

/-- Remove the additive source using its individual trivial model. -/
def additiveRemovalEquiv (A B L : FDRep k G)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k)) :
    Representation.Equiv (tensor (tensor A (dualRepresentation B)) L).ρ
      (tensor A (dualRepresentation B)).ρ :=
  (tensorEquiv (A := tensor A (dualRepresentation B))
    (B := tensor A (dualRepresentation B)) (D := FDRep.of (Representation.trivial k G k))
    (Representation.Equiv.refl _) hL).trans
    (Representation.TensorProduct.rid k (tensor A (dualRepresentation B)).ρ)

theorem additiveRemovalEquiv_natural (A B L : FDRep k G)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k))
    (t : Module.End k (tensor A (dualRepresentation B)).V) (s : Module.End k L.V)
    (h : ∀ x, hL (s x) = hL x)
    (x : (tensor (tensor A (dualRepresentation B)) L).V) :
    additiveRemovalEquiv A B L hL (TensorProduct.map t s x) =
      t (additiveRemovalEquiv A B L hL x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change hL (s y) • t x = t (hL y • x)
    rw [h, t.map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {rho : Representation k G (ModelSpace (k := k))}

/-- The same source comparisons as in `inputInvariantsEquiv`, before
restricting to invariants and passing to matrices. -/
def sourceTensorEquiv (A B L : FDRep k G)
    (hA : Representation.Equiv A.ρ rho) (hB : Representation.Equiv B.ρ rho)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k)) :
    Representation.Equiv (tensor (tensor A (dualRepresentation B)) L).ρ
      (rho.tprod rho.dual) :=
  (additiveRemovalEquiv A B L hL).trans
    (tensorEquiv (B := FDRep.of rho) hA (dualEquiv (B := FDRep.of rho) hB))

theorem sourceTensorEquiv_natural (A B L : FDRep k G)
    (hA : Representation.Equiv A.ρ rho) (hB : Representation.Equiv B.ρ rho)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k))
    (sA : A.V ≃ₗ[k] A.V) (sB : B.V ≃ₗ[k] B.V) (sL : Module.End k L.V)
    (tA tB : ModelSpace (k := k) ≃ₗ[k] ModelSpace (k := k))
    (ha : ∀ x, hA (sA x) = tA (hA x)) (hb : ∀ x, hB (sB x) = tB (hB x))
    (hl : ∀ x, hL (sL x) = hL x)
    (x : (tensor (tensor A (dualRepresentation B)) L).V) :
    sourceTensorEquiv A B L hA hB hL
        (TensorProduct.map (TensorProduct.map sA.toLinearMap sB.symm.toLinearMap.dualMap) sL x) =
      TensorProduct.map tA.toLinearMap tB.symm.toLinearMap.dualMap
        (sourceTensorEquiv A B L hA hB hL x) := by
  exact (congrArg (tensorEquiv (B := FDRep.of rho) hA (dualEquiv (B := FDRep.of rho) hB))
    (additiveRemovalEquiv_natural A B L hL
      (TensorProduct.map sA.toLinearMap sB.symm.toLinearMap.dualMap) sL hl x)).trans
    (tensorEquiv_natural (B := FDRep.of rho) hA (dualEquiv (B := FDRep.of rho) hB)
      sA.toLinearMap sB.symm.toLinearMap.dualMap tA.toLinearMap tB.symm.toLinearMap.dualMap
      ha (dualEquiv_natural (B := FDRep.of rho) hB sB tB hb) (additiveRemovalEquiv A B L hL x))

/-- The new raw comparison is exactly the previously used invariant
coordinates, rather than a separately chosen boundary identification. -/
theorem inputInvariantsEquiv_val (M : RegularModel rho) (A B L : FDRep k G)
    (hA : Representation.Equiv A.ρ rho) (hB : Representation.Equiv B.ρ rho)
    (hL : Representation.Equiv L.ρ (Representation.trivial k G k))
    (x : Representation.invariants (tensor (tensor A (dualRepresentation B)) L).ρ) :
    (inputInvariantsEquiv M A B L hA hB hL x).val =
      tensorMatrixEquiv (sourceTensorEquiv A B L hA hB hL x.val) := rfl

section CurveRestriction

open CategoryTheory PublishedPhysicalConstruction BoundaryFromSourceModels

variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{w} ℂ} {S : BoundarySequence D H F}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F S)

/-- General arithmetic restriction laws for all inputs. These specify
only tensor/dual naturality, not a formula for the Kloosterman recipe. -/
structure ArithmeticRestriction where
  zeroFr : ∀ A, (Z.zero A).V ≃ₗ[ℂ] (Z.zero A).V
  tensor_natural : ∀ A B x,
    Z.tensorZero A B (zeroFr (D.tensor A B) x) =
      TensorProduct.map (zeroFr A).toLinearMap (zeroFr B).toLinearMap (Z.tensorZero A B x)
  dual_natural : ∀ A (hA : D.Lisse A) x,
    Z.dualZero A hA (zeroFr (D.dual A) x) =
      (zeroFr A).symm.toLinearMap.dualMap (Z.dualZero A hA x)

variable (P : ArithmeticRestriction Z) (K : KloostermanInputData D)

omit [Abelian C] in
/-- Derive the Frobenius operator on the literal input from the general
restriction laws; the dual factor has the inverse operator. -/
theorem zeroInputEquiv_natural (x : (Z.zero K.input).V) :
    zeroInputEquiv Z K (P.zeroFr K.input x) =
      TensorProduct.map
        (TensorProduct.map (P.zeroFr K.first).toLinearMap
          (P.zeroFr K.second).symm.toLinearMap.dualMap)
        (P.zeroFr K.additive).toLinearMap (zeroInputEquiv Z K x) := by
  let inner := (Z.tensorZero K.first (D.dual K.second)).trans
    (tensorEquiv (A := Z.zero K.first) (B := Z.zero K.first)
      (Representation.Equiv.refl (Z.zero K.first).ρ) (Z.dualZero K.second K.second_lisse))
  have hi : ∀ y, inner (P.zeroFr (D.tensor K.first (D.dual K.second)) y) =
      TensorProduct.map (P.zeroFr K.first).toLinearMap
        (P.zeroFr K.second).symm.toLinearMap.dualMap (inner y) := by
    intro y
    exact (congrArg (tensorEquiv (A := Z.zero K.first) (B := Z.zero K.first)
      (Representation.Equiv.refl _) (Z.dualZero K.second K.second_lisse))
      (P.tensor_natural K.first (D.dual K.second) y)).trans
      (tensorEquiv_natural (A := Z.zero K.first) (B := Z.zero K.first)
        (Representation.Equiv.refl _) (Z.dualZero K.second K.second_lisse)
        (P.zeroFr K.first).toLinearMap (P.zeroFr (D.dual K.second)).toLinearMap
        (P.zeroFr K.first).toLinearMap (P.zeroFr K.second).symm.toLinearMap.dualMap
        (fun _ => rfl) (P.dual_natural K.second K.second_lisse) (Z.tensorZero K.first (D.dual K.second) y))
  exact (congrArg (tensorEquiv inner (C := Z.zero K.additive) (D := Z.zero K.additive)
    (Representation.Equiv.refl _))
    (P.tensor_natural (D.tensor K.first (D.dual K.second)) K.additive x)).trans
    (tensorEquiv_natural inner (C := Z.zero K.additive) (D := Z.zero K.additive)
      (Representation.Equiv.refl _)
      (P.zeroFr (D.tensor K.first (D.dual K.second))).toLinearMap (P.zeroFr K.additive).toLinearMap
      (TensorProduct.map (P.zeroFr K.first).toLinearMap (P.zeroFr K.second).symm.toLinearMap.dualMap)
      (P.zeroFr K.additive).toLinearMap hi (fun _ => rfl)
      (Z.tensorZero (D.tensor K.first (D.dual K.second)) K.additive x))

end CurveRestriction

end PrimeGap182.TypeIII.RestrictionFrobenius

#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.tensorEquiv_natural
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.inverse_natural
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.dualEquiv_natural
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.additiveRemovalEquiv
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.additiveRemovalEquiv_natural
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.sourceTensorEquiv
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.sourceTensorEquiv_natural
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.inputInvariantsEquiv_val
#print axioms PrimeGap182.TypeIII.RestrictionFrobenius.zeroInputEquiv_natural
