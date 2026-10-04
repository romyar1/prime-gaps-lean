import TypeIIISelectedTensorTransport
import TypeIIIPublishedMackey
import Mathlib.Data.List.NodupEquivFin

/-!
# The iterated physical tensor is the selected tensor representation

All comparisons here are constructed from actual equivariant maps. The
proof includes the empty tensor, removes one factor at a time, and
reindexes list positions to the selected finite subset. This closes the
gap between the physical construction's monoidal fold and the phase
theorem's PiTensorProduct. No finite-tensor comparison is an assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.TensorListRepresentation

open PublishedPhaseApplication PublishedPhysicalConstruction SelectedTensorTransport

universe u v w z
variable {E : Type u} [Field E] {G : Type v} [Group G]

def equivOfIso {V W : FDRep E G} (e : V ≅ W) : Representation.Equiv V.ρ W.ρ :=
  Representation.equivOfIso ((forget₂ (FDRep E G) (Rep E G)).mapIso e)

/-- The existing categorical binary tensor has the usual diagonal action. -/
def monoidalTensorEquiv (V W : FDRep E G) :
    Representation.Equiv (V ⊗ W).ρ (PublishedMackey.tensor V W).ρ :=
  .refl _

def indexedTensorEmptyEquiv {ι : Type} [Fintype ι] [IsEmpty ι] (V : ι → FDRep E G) :
    Representation.Equiv (indexedTensor V).ρ (𝟙_ (FDRep E G)).ρ where
  toLinearEquiv := PiTensorProduct.isEmptyEquiv ι
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    change PiTensorProduct.isEmptyEquiv ι
      (PiTensorProduct.map (fun i => (V i).ρ g) (PiTensorProduct.tprod E m)) =
        PiTensorProduct.isEmptyEquiv ι (PiTensorProduct.tprod E m)
    simp only [PiTensorProduct.map_tprod, PiTensorProduct.isEmptyEquiv_apply_tprod]

/-- Split off one selected factor, preserving the diagonal group action. -/
def indexedTensorSplit {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → FDRep E G) (i₀ : ι) :
    Representation.Equiv (indexedTensor V).ρ
      (PublishedMackey.tensor (V i₀)
        (indexedTensor (fun j : ({i₀}ᶜ : Set ι) => V j))).ρ where
  toLinearEquiv := (PiTensorProduct.equivPiTensorComplSingletonTensor E (fun i => (V i).V) i₀).trans
    (TensorProduct.comm E _ _)
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    change (TensorProduct.comm E _ _)
      (PiTensorProduct.equivPiTensorComplSingletonTensor E (fun i => (V i).V) i₀
        (PiTensorProduct.map (fun i => (V i).ρ g) (PiTensorProduct.tprod E m))) =
      TensorProduct.map ((V i₀).ρ g)
        (PiTensorProduct.map (fun j : ({i₀}ᶜ : Set ι) => (V j).ρ g))
        ((TensorProduct.comm E _ _)
          (PiTensorProduct.equivPiTensorComplSingletonTensor E (fun i => (V i).V) i₀
            (PiTensorProduct.tprod E m)))
    simp only [PiTensorProduct.map_tprod,
      PiTensorProduct.equivPiTensorComplSingletonTensor_tprod,
      TensorProduct.comm_tmul, TensorProduct.map_tmul]
    congr 1
    exact (PiTensorProduct.map_tprod
      (fun j : ({i₀}ᶜ : Set ι) => (V j).ρ g) (fun j => m j)).symm

def tailEquiv (n : ℕ) : Fin n ≃ ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1))) where
  toFun i := ⟨i.succ, Fin.succ_ne_zero i⟩
  invFun i := i.val.pred i.property
  left_inv i := Fin.pred_succ i
  right_inv i := by apply Subtype.ext; exact Fin.succ_pred i.val i.property

def indexedTensorConsEquiv (V : Fin 4 → FDRep E G) (i : Fin 4) (is : List (Fin 4)) :
    Representation.Equiv
      (indexedTensor (fun j : Fin (i :: is).length => V ((i :: is).get j))).ρ
      (PublishedMackey.tensor (V i) (indexedTensor (fun j : Fin is.length => V (is.get j)))).ρ := by
  let tail := indexedTensorEquiv (fun j : Fin is.length => V (is.get j))
    (fun j : ({(0 : Fin (is.length + 1))}ᶜ : Set (Fin (is.length + 1))) => V ((i :: is).get j))
    (tailEquiv is.length) (fun _ => Representation.Equiv.refl _)
  exact (indexedTensorSplit (fun j : Fin (i :: is).length => V ((i :: is).get j)) 0).trans
    (PublishedMackey.tensorEquiv (Representation.Equiv.refl _) tail.symm)

/-- Induction on the literal list used by the physical construction. -/
def tensorListIndexedEquiv (V : Fin 4 → FDRep E G) : (is : List (Fin 4)) →
    Representation.Equiv (tensorList V is).ρ
      (indexedTensor (fun j : Fin is.length => V (is.get j))).ρ
  | [] => (indexedTensorEmptyEquiv (ι := Fin 0) _).symm
  | i :: is => (monoidalTensorEquiv (V i) (tensorList V is)).trans
      ((PublishedMackey.tensorEquiv (Representation.Equiv.refl _) (tensorListIndexedEquiv V is)).trans
        (indexedTensorConsEquiv V i is).symm)

def subsetPositionsEquiv (S : Finset (Fin 4)) : Fin S.toList.length ≃ S :=
  (List.Nodup.getEquiv S.toList S.nodup_toList).trans
    (Equiv.subtypeEquivRight (fun _ => Finset.mem_toList))

/-- The original categorical finite tensor and the exact selected tensor
used in the phase application are equivalent as representations. -/
def tensorSubsetEquiv (V : Fin 4 → FDRep E G) (S : Finset (Fin 4)) :
    Representation.Equiv (tensorSubset V S).ρ (selectedTensor S V).ρ :=
  (tensorListIndexedEquiv V S.toList).trans
    (indexedTensorEquiv (fun j : Fin S.toList.length => V (S.toList.get j)) (fun i : S => V i)
      (subsetPositionsEquiv S) (fun _ => Representation.Equiv.refl _))

variable {C : Type w} [Category.{z} C] [MonoidalCategory C]

/-- The finite tensor comparison is derived from an actual strong monoidal
inertia functor, rather than included among its realization assumptions. -/
def monoidalSelectedTensorEquiv (F : C ⥤ FDRep E G) [F.Monoidal]
    (V : Fin 4 → C) (S : Finset (Fin 4)) :
    Representation.Equiv (F.obj (tensorSubset V S)).ρ
      (selectedTensor S (fun i => F.obj (V i))).ρ :=
  (equivOfIso (tensorSubsetMapIso F V S)).trans
    (tensorSubsetEquiv (fun i => F.obj (V i)) S)

end PrimeGap182.TypeIII.TensorListRepresentation

#print axioms PrimeGap182.TypeIII.TensorListRepresentation.equivOfIso
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.monoidalTensorEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.indexedTensorEmptyEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.indexedTensorSplit
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.tailEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.indexedTensorConsEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.tensorListIndexedEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.subsetPositionsEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.tensorSubsetEquiv
#print axioms PrimeGap182.TypeIII.TensorListRepresentation.monoidalSelectedTensorEquiv
