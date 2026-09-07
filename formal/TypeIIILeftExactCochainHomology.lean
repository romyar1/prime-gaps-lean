import TypeIIIExactResolutionCycles
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Homology of the literal image of a nonnegative cochain complex

A left exact additive functor preserves the actual cycle kernels.  Consequently,
a cokernel of the mapped differential into the next cycles computes the positive
homology of the mapped complex.  The construction below identifies the action
of the original cochain map on this homology.  In degree zero, an isomorphism on
the original cycles remains a quasi-isomorphism after applying the functor.

The cokernel data in the positive-degree construction are explicit universal
properties.  In the acyclic-resolution application they will be obtained from
the proved ordinary long exact sequence.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

set_option backward.isDefEq.respectTransparency false in
/-- The image of the actual cycle inclusion is a kernel of the mapped differential. -/
def leftExactCochainCyclesIsKernel (K : CochainComplex C ℕ) (n : ℕ) :
    IsLimit (KernelFork.ofι (F.map (K.iCycles n))
      (by rw [← F.map_comp, K.iCycles_d n (n + 1), F.map_zero])) :=
  KernelFork.mapIsLimit _ (K.cyclesIsKernel n (n + 1) (by simp)) F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- An actual cokernel of the mapped differential into cycles gives left homology
data for the original mapped complex in the following degree. -/
def leftExactCochainHomologyData (K : CochainComplex C ℕ) (n : ℕ) {H : D}
    (π : F.obj (K.cycles (n + 1)) ⟶ H)
    (w : F.map (K.toCycles n (n + 1)) ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π w)) :
    (((F.mapHomologicalComplex (.up ℕ)).obj K).sc' n (n + 1) (n + 2)).LeftHomologyData := by
  let S := ((F.mapHomologicalComplex (.up ℕ)).obj K).sc' n (n + 1) (n + 2)
  let hi := leftExactCochainCyclesIsKernel F K (n + 1)
  have hf : hi.lift (KernelFork.ofι S.f S.zero) = F.map (K.toCycles n (n + 1)) := by
    apply Fork.IsLimit.hom_ext hi
    rw [Fork.IsLimit.lift_ι]
    change F.map (K.d n (n + 1)) =
      F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1))
    rw [← F.map_comp, K.toCycles_i]
  refine
    { K := F.obj (K.cycles (n + 1))
      H := H
      i := F.map (K.iCycles (n + 1))
      π := π
      wi := by
        change F.map (K.iCycles (n + 1)) ≫ F.map (K.d (n + 1) (n + 2)) = 0
        rw [← F.map_comp, K.iCycles_d, F.map_zero]
      hi := hi
      wπ := ?_
      hπ := ?_ }
  · change hi.lift (KernelFork.ofι S.f S.zero) ≫ π = 0
    rw [hf]
    exact w
  · change IsColimit (CokernelCofork.ofπ π
      (show hi.lift (KernelFork.ofι S.f S.zero) ≫ π = 0 from by rw [hf]; exact w))
    have transfer : ∀ (d : F.obj (K.X n) ⟶ F.obj (K.cycles (n + 1)))
        (_ : d = F.map (K.toCycles n (n + 1))) (w' : d ≫ π = 0),
        IsColimit (CokernelCofork.ofπ π w') := by
      intro d hd w'
      subst d
      exact hc
    exact transfer _ hf _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The incoming boundary in these homology data is the actual mapped map into cycles. -/
theorem leftExactCochainHomologyData_f' (K : CochainComplex C ℕ) (n : ℕ) {H : D}
    (π : F.obj (K.cycles (n + 1)) ⟶ H)
    (w : F.map (K.toCycles n (n + 1)) ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π w)) :
    (leftExactCochainHomologyData F K n π w hc).f' = F.map (K.toCycles n (n + 1)) := by
  apply (cancel_mono (F.map (K.iCycles (n + 1)))).1
  change (leftExactCochainHomologyData F K n π w hc).f' ≫
      (leftExactCochainHomologyData F K n π w hc).i = _
  rw [ShortComplex.LeftHomologyData.f'_i]
  change F.map (K.d n (n + 1)) =
    F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1))
  rw [← F.map_comp, K.toCycles_i]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- A commuting map of the actual cokernels describes the homology map of the
literal image of the original cochain map. -/
def leftExactCochainHomologyMapData {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)
    {H₁ H₂ : D} (π₁ : F.obj (K.cycles (n + 1)) ⟶ H₁)
    (w₁ : F.map (K.toCycles n (n + 1)) ≫ π₁ = 0)
    (hc₁ : IsColimit (CokernelCofork.ofπ π₁ w₁))
    (π₂ : F.obj (L.cycles (n + 1)) ⟶ H₂)
    (w₂ : F.map (L.toCycles n (n + 1)) ≫ π₂ = 0)
    (hc₂ : IsColimit (CokernelCofork.ofπ π₂ w₂))
    (u : H₁ ⟶ H₂)
    (hu : π₁ ≫ u = F.map (cyclesMap φ (n + 1)) ≫ π₂) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' D (.up ℕ) n (n + 1) (n + 2)).map
        ((F.mapHomologicalComplex (.up ℕ)).map φ))
      (leftExactCochainHomologyData F K n π₁ w₁ hc₁)
      (leftExactCochainHomologyData F L n π₂ w₂ hc₂) where
  φK := F.map (cyclesMap φ (n + 1))
  φH := u
  commi := by
    change F.map (cyclesMap φ (n + 1)) ≫ F.map (L.iCycles (n + 1)) =
      F.map (K.iCycles (n + 1)) ≫ F.map (φ.f (n + 1))
    rw [← F.map_comp, ← F.map_comp, cyclesMap_i]
  commf' := by
    rw [leftExactCochainHomologyData_f', leftExactCochainHomologyData_f']
    change F.map (K.toCycles n (n + 1)) ≫ F.map (cyclesMap φ (n + 1)) =
      F.map (φ.f n) ≫ F.map (L.toCycles n (n + 1))
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (cochainCyclesSequenceMap φ n).comm₂₃.symm
  commπ := hu

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism on these proved cokernels is a quasi-isomorphism in the
corresponding positive degree of the original mapped cochain map. -/
theorem leftExactCochain_quasiIsoAt_succ_of_cokernel {K L : CochainComplex C ℕ}
    (φ : K ⟶ L) (n : ℕ) {H₁ H₂ : D}
    (π₁ : F.obj (K.cycles (n + 1)) ⟶ H₁)
    (w₁ : F.map (K.toCycles n (n + 1)) ≫ π₁ = 0)
    (hc₁ : IsColimit (CokernelCofork.ofπ π₁ w₁))
    (π₂ : F.obj (L.cycles (n + 1)) ⟶ H₂)
    (w₂ : F.map (L.toCycles n (n + 1)) ≫ π₂ = 0)
    (hc₂ : IsColimit (CokernelCofork.ofπ π₂ w₂))
    (u : H₁ ⟶ H₂) [IsIso u]
    (hu : π₁ ≫ u = F.map (cyclesMap φ (n + 1)) ≫ π₂) :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map φ) (n + 1) := by
  rw [quasiIsoAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  exact (leftExactCochainHomologyMapData F φ n π₁ w₁ hc₁ π₂ w₂ hc₂ u hu).quasiIso_iff.mpr
    (inferInstanceAs (IsIso u))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The original zero-cycle map, when invertible, remains a homology isomorphism
in degree zero after applying the left exact functor. -/
theorem leftExactCochain_quasiIsoAt_zero {K L : CochainComplex C ℕ} (φ : K ⟶ L)
    [IsIso (cyclesMap φ 0)] : QuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map φ) 0 := by
  let S₁ := ((F.mapHomologicalComplex (.up ℕ)).obj K).sc' 0 0 1
  let S₂ := ((F.mapHomologicalComplex (.up ℕ)).obj L).sc' 0 0 1
  have hf₁ : S₁.f = 0 := by change F.map (K.d 0 0) = 0; simp
  have hf₂ : S₂.f = 0 := by change F.map (L.d 0 0) = 0; simp
  let c₁ : KernelFork S₁.g := KernelFork.ofι (F.map (K.iCycles 0))
    (by
      change F.map (K.iCycles 0) ≫ F.map (K.d 0 1) = 0
      rw [← F.map_comp, K.iCycles_d, F.map_zero])
  let c₂ : KernelFork S₂.g := KernelFork.ofι (F.map (L.iCycles 0))
    (by
      change F.map (L.iCycles 0) ≫ F.map (L.d 0 1) = 0
      rw [← F.map_comp, L.iCycles_d, F.map_zero])
  let χ := (shortComplexFunctor' D (.up ℕ) 0 0 1).map
    ((F.mapHomologicalComplex (.up ℕ)).map φ)
  let γ := ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork χ
    hf₁ c₁ (leftExactCochainCyclesIsKernel F K 0)
    hf₂ c₂ (leftExactCochainCyclesIsKernel F L 0)
    (F.map (cyclesMap φ 0)) (by
      change F.map (K.iCycles 0) ≫ F.map (φ.f 0) =
        F.map (cyclesMap φ 0) ≫ F.map (L.iCycles 0)
      rw [← F.map_comp, ← F.map_comp, cyclesMap_i])
  rw [CochainComplex.quasiIsoAt₀_iff]
  exact γ.quasiIso_iff.mpr (inferInstanceAs (IsIso (F.map (cyclesMap φ 0))))

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.leftExactCochainCyclesIsKernel
#print axioms PrimeGap182.TypeIII.leftExactCochainHomologyData
#print axioms PrimeGap182.TypeIII.leftExactCochainHomologyData_f'
#print axioms PrimeGap182.TypeIII.leftExactCochainHomologyMapData
#print axioms PrimeGap182.TypeIII.leftExactCochain_quasiIsoAt_succ_of_cokernel
#print axioms PrimeGap182.TypeIII.leftExactCochain_quasiIsoAt_zero
