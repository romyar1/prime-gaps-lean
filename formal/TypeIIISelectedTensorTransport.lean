import TypeIIIPublishedPhysicalConstruction
import TypeIIIPublishedApplicationBridge
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transporting actual tensor representations

The finite tensor equivalences below use Mathlib's PiTensorProduct and
its diagonal action. Reindexing preserves the group action. In particular,
the cyclic Fin 4 order is explicitly matched to the rectangle convention
of the existing Type III phase theorem. No phase-containment law is used.

The separate monoidal-functor lemma transports the existing tensorList.
Connecting this iterated categorical tensor to the selected PiTensorProduct,
and instantiating the geometric inertia functor, are separate steps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.SelectedTensorTransport

open PublishedPhaseApplication PublishedTypeIII PublishedApplicationBridge
open PublishedPhysicalConstruction

universe u v w z
variable {E : Type u} [Field E] {G : Type v} [Group G]

def representationEquivOfEq {V W : FDRep E G} (h : V = W) : Representation.Equiv V.ρ W.ρ := by
  subst W
  exact .refl _

/-- The actual tensor of an arbitrary finite indexed family. -/
def indexedTensor {ι : Type} [Fintype ι] (V : ι → FDRep E G) : FDRep E G :=
  FDRep.of ({
    toFun g := PiTensorProduct.map (fun i => (V i).ρ g)
    map_one' := by simp only [map_one, PiTensorProduct.map_one]
    map_mul' g h := by simp only [map_mul, PiTensorProduct.map_mul]
  } : Representation E G (PiTensorProduct E (fun i => (V i).V)))

/-- Tensor an actual family of equivariant equivalences. -/
def indexedTensorCongr {ι : Type} [Fintype ι] {V W : ι → FDRep E G}
    (h : ∀ i, Representation.Equiv (V i).ρ (W i).ρ) :
    Representation.Equiv (indexedTensor V).ρ (indexedTensor W).ρ where
  toLinearEquiv := PiTensorProduct.congr (fun i => (h i).toLinearEquiv)
  isIntertwining' g := by
    change PiTensorProduct.map (fun i => (h i).toLinearMap) ∘ₗ
        PiTensorProduct.map (fun i => (V i).ρ g) =
      PiTensorProduct.map (fun i => (W i).ρ g) ∘ₗ
        PiTensorProduct.map (fun i => (h i).toLinearMap)
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    congr 1
    funext i
    exact (h i).isIntertwining' g

/-- Reindexing is equivariant for the actual diagonal tensor action. -/
def indexedTensorReindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (V : ι → FDRep E G) (e : ι ≃ κ) :
    Representation.Equiv (indexedTensor V).ρ (indexedTensor (fun j => V (e.symm j))).ρ where
  toLinearEquiv := PiTensorProduct.reindex E (fun i => (V i).V) e
  isIntertwining' g := by
    exact (PiTensorProduct.map_comp_reindex_eq (fun i => (V i).ρ g) e).symm

/-- Reindex and then transport the entries, retaining their group actions. -/
def indexedTensorEquiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (V : ι → FDRep E G) (W : κ → FDRep E G) (e : ι ≃ κ)
    (h : ∀ i, Representation.Equiv (V i).ρ (W (e i)).ρ) :
    Representation.Equiv (indexedTensor V).ρ (indexedTensor W).ρ :=
  (indexedTensorReindex V e).trans (indexedTensorCongr (fun j =>
    (h (e.symm j)).trans (representationEquivOfEq (congrArg W (e.apply_symm_apply j)))))

/-- The actual selected subtypes in cyclic and rectangle conventions. -/
def cycleSubsetEquiv (S : Finset (Fin 4)) : S ≃ rectangleSubset S where
  toFun i := ⟨cycleRectangle i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  invFun e := ⟨cycleRectangle.symm e, by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp e.property
    simpa only [← he, cycleRectangle.symm_apply_apply] using hi⟩
  left_inv i := by apply Subtype.ext; exact cycleRectangle.symm_apply_apply i
  right_inv e := by apply Subtype.ext; exact cycleRectangle.apply_symm_apply e

/-- The tensor family used by the phase calculation has exactly the
selected cyclic entries, with an explicit equivariant reindexing. -/
def selectedCycleEquiv (S : Finset (Fin 4)) (V : Fin 4 → FDRep E G)
    (W : PhaseRectangle → FDRep E G)
    (h : ∀ i, Representation.Equiv (V i).ρ (W (cycleRectangle i)).ρ) :
    Representation.Equiv (selectedTensor S V).ρ (selectedTensor (rectangleSubset S) W).ρ :=
  indexedTensorEquiv (fun i : S => V i) (fun e : rectangleSubset S => W e)
    (cycleSubsetEquiv S) (fun i => h i)

/-- A genuine equivalence supplies the actual injective/surjective
equivariant maps in the existing subquotient predicate. -/
theorem isSubquotient_of_equiv {V W : FDRep E G} (h : Representation.Equiv V.ρ W.ρ) :
    IsSubquotient V W := by
  refine ⟨V, h.toIntertwiningMap, Representation.IntertwiningMap.id V.ρ, ?_, ?_⟩
  · exact h.toLinearEquiv.injective
  · exact Function.surjective_id

section MonoidalTransport

variable {C : Type w} [Category.{z} C] [MonoidalCategory C]
  {B : Type u} [Category.{v} B] [MonoidalCategory B]

/-- A strong monoidal functor transports the literal iterated tensor in
the existing physical construction, including the empty subset. -/
def tensorListMapIso (F : C ⥤ B) [F.Monoidal] (V : Fin 4 → C) :
    (is : List (Fin 4)) → F.obj (tensorList V is) ≅ tensorList (fun i => F.obj (V i)) is
  | [] => (Functor.Monoidal.εIso F).symm
  | i :: is => (Functor.Monoidal.μIso F (V i) (tensorList V is)).symm ≪≫
      (Iso.refl (F.obj (V i)) ⊗ᵢ tensorListMapIso F V is)

def tensorSubsetMapIso (F : C ⥤ B) [F.Monoidal] (V : Fin 4 → C) (S : Finset (Fin 4)) :
    F.obj (tensorSubset V S) ≅ tensorSubset (fun i => F.obj (V i)) S :=
  tensorListMapIso F V S.toList

end MonoidalTransport
end PrimeGap182.TypeIII.SelectedTensorTransport

#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.indexedTensorCongr
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.representationEquivOfEq
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.indexedTensorReindex
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.indexedTensorEquiv
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.cycleSubsetEquiv
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.selectedCycleEquiv
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.isSubquotient_of_equiv
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.tensorListMapIso
#print axioms PrimeGap182.TypeIII.SelectedTensorTransport.tensorSubsetMapIso
