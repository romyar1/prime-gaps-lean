import TypeIIITensorListRepresentation

/-!
# Deriving the physical local tensor comparison

The comparison for every selected subset is derived from an actual
strong monoidal inertia functor, general restriction/dual-Tate compatibility,
and the four individual core identifications. The monoidal fold, tensor
unit, diagonal group actions, conjugated corners, and rectangle reindexing
are all handled by constructed equivariant equivalences.

This removes the finite-family tensor comparison as an independent input.
The four geometric core identifications and the intended compatible inertia
realization still have to be constructed. No local Fourier or phase bound
is assumed in this tensor step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.PhysicalTensorComparison

open PublishedPhysicalConstruction PublishedPhaseApplication PublishedTypeIII
open PublishedApplicationBridge SelectedTensorTransport TensorListRepresentation

universe u v w z a b c

variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  {E : Type a} [Field E] {Γ : Type b} [Group Γ]
  {Obj : Type c} {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : PublishedSupportRules.RationalStalkRealization p SD}

/-- General compatibility on all lisse parameter objects. The punctured
radial curve lies in the torus, so IC restricts to the original object.
The unramified Tate twist is invisible to geometric wild inertia. -/
structure InertiaCompatibility (I : C ⥤ FDRep E Γ)
    (IC : IntermediateExtensionData realization C) (radial : Obj → FDRep E Γ)
    (P : ParameterData C) where
  restriction : ∀ A, P.Lisse A → Representation.Equiv (radial (IC.geometric A)).ρ (I.obj A).ρ
  dualTate : ∀ A, P.Lisse A →
    Representation.Equiv (I.obj (P.dualTateMinusOne A)).ρ (dualRepresentation (I.obj A)).ρ

variable (K : KloostermanInputData D) (R : CurveRules D) (Hrules : CohomologyRules D H P)
  (O : TorusOperationData p C) (T : TorusArithmeticData p C) (TR : TorusRules P O T)
  (I : C ⥤ FDRep E Γ) [I.Monoidal]
  (IC : IntermediateExtensionData realization C) (radial : Obj → FDRep E Γ)
  (IR : InertiaCompatibility I IC radial P)
  (α m m' n n' : (ZMod p)ˣ)

/-- The unconjugated entries, indexed by the original two rows and columns. -/
def matrixEntry (e : PhaseRectangle) : C :=
  pulledEntry (H := H) (P := P) K O α (![m, m'] e.1) (![n, n'] e.2)

variable (cores : PhaseRectangle → FDRep E Γ)
  (hcore : ∀ e, Representation.Equiv
    (I.obj (matrixEntry (H := H) (P := P) K O α m m' n n' e)).ρ (cores e).ρ)

/-- Apply dual-Tate compatibility at exactly the two conjugated corners. -/
def entryEquiv (i : Fin 4) :
    Representation.Equiv
      (I.obj (entryObjects (H := H) (P := P) K O α m m' n n' i)).ρ
      (signedRepresentation (conjugatedCorner (cycleRectangle i)) (cores (cycleRectangle i))).ρ := by
  apply Classical.choice
  fin_cases i
  · exact ⟨hcore (0, 0)⟩
  · exact ⟨(IR.dualTate _ (pulledEntry_lisse K R Hrules O T TR α m' n)).trans
      (PublishedMackey.dualEquiv (hcore (1, 0)))⟩
  · exact ⟨hcore (1, 1)⟩
  · exact ⟨(IR.dualTate _ (pulledEntry_lisse K R Hrules O T TR α m n')).trans
      (PublishedMackey.dualEquiv (hcore (0, 1)))⟩

/-- The exact physical IC family is equivalent to the selected rectangle
tensor. No subset-by-subset comparison is supplied. -/
def physicalTensorEquiv (S : Finset (Fin 4)) :
    Representation.Equiv
      (radial (physicalObjects IC (entryObjects (H := H) (P := P) K O α m m' n n') S)).ρ
      (selectedTensor (rectangleSubset S)
        (fun e => signedRepresentation (conjugatedCorner e) (cores e))).ρ := by
  let V := entryObjects (H := H) (P := P) K O α m m' n n'
  have hl := tensorSubset_lisse TR V (entryObjects_lisse K R Hrules O T TR α m m' n n') S
  exact (IR.restriction (tensorSubset V S) hl).trans
    ((monoidalSelectedTensorEquiv I V S).trans
      (selectedCycleEquiv S (fun i => I.obj (V i))
        (fun e => signedRepresentation (conjugatedCorner e) (cores e))
        (entryEquiv K R Hrules O T TR I IC radial IR α m m' n n' cores hcore)))

include R Hrules TR IR hcore in
/-- This has the precise subquotient shape required by
`LocalFamilyData.tensor_comparison`, and holds even for the empty subset. -/
theorem physical_tensor_comparison (S : Finset (Fin 4)) :
    IsSubquotient
      (radial (physicalObjects IC (entryObjects (H := H) (P := P) K O α m m' n n') S))
      (selectedTensor (rectangleSubset S)
        (fun e => signedRepresentation (conjugatedCorner e) (cores e))) :=
  isSubquotient_of_equiv
    (physicalTensorEquiv K R Hrules O T TR I IC radial IR α m m' n n' cores hcore S)

end PrimeGap182.TypeIII.PhysicalTensorComparison

#print axioms PrimeGap182.TypeIII.PhysicalTensorComparison.entryEquiv
#print axioms PrimeGap182.TypeIII.PhysicalTensorComparison.physicalTensorEquiv
#print axioms PrimeGap182.TypeIII.PhysicalTensorComparison.physical_tensor_comparison
