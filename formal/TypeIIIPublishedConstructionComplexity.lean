import TypeIIIPublishedPhysicalConstruction
import TypeIIIPublishedPolynomialComplexity
import TypeIIIPublishedUniformComplexity

/-!
# Complexity of the literal physical Type III construction

This module derives the physical complexity cap, rather than taking the cap
of the finished IC objects as a hypothesis. It follows the existing input
term, categorical image, genuine physical morphisms, signed and conjugated
entries, actual finite tensor, and intermediate extension.

A common function f bounds the finitely many general operations below.
QST Theorems 6.8 and 6.15, Proposition 6.24, and the fixed presentations
supply such a function, uniformly at the fixed embedding dimensions. It is
not assumed monotone: each step uses a finite upper envelope. The polynomial
morphism bound is applied through the existing theorem to the actual map.

The remaining source obligation is explicit: bound K.first, K.second and
K.additive as the actual Kl3/AS pullbacks. No claim here constructs those
starting sheaves or the common geometric/inertia realization. No Fourier
estimate is an input or a conclusion of this module.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Classical MonoidalCategory
namespace PrimeGap182.TypeIII.PublishedConstructionComplexity

open PublishedPhysicalConstruction PublishedPolynomialComplexity
open PublishedUniformComplexity

/-- Thirteen monotone-envelope steps will cover the actual construction. -/
def budget (f : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => start
  | n + 1 => max (budget f start n) (envelope f (budget f start n))

theorem budget_mono (f : ℕ → ℕ) (start : ℕ) : Monotone (budget f start) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem operation_le_budget (f : ℕ → ℕ) (start n c : ℕ)
    (hc : c ≤ budget f start n) : f c ≤ budget f start (n+1) :=
  (le_envelope f hc).trans (le_max_right _ _)

def initialCap (sourceCap unitCap : ℕ) : ℕ :=
  max sourceCap (max unitCap 34646092416)

def physicalCap (f : ℕ → ℕ) (sourceCap unitCap : ℕ) : ℕ :=
  budget f (initialCap sourceCap unitCap) 13

universe u v w z a
variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  {Obj : Type a} {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : PublishedSupportRules.RationalStalkRealization p SD}

/-- General complexity rules for every input and every morphism of the
specified spaces. The image bound concerns the actual categorical image
of any map between lisse sheaves; shifted by two it is a perverse
subquotient of its source. There is no rule about a finished Type III family. -/
structure OperationBounds (f : ℕ → ℕ) (unitCap : ℕ)
    (ci : Input → ℕ) (cp : C → ℕ)
    (cm : TorusMorphismComplexity (ZMod p))
    (O : TorusOperationData p C) (IC : IntermediateExtensionData realization C) : Prop where
  input_dual : ∀ A, D.Lisse A → ci (D.dual A) ≤ f (ci A)
  input_tensor : ∀ A B, D.Lisse A → D.Lisse B →
    ci (D.tensor A B) ≤ f (max (ci A) (ci B))
  compact : ∀ A, D.Lisse A → cp (H.compact A) ≤ f (ci A)
  image : ∀ A B (g : A ⟶ B), P.Lisse A → P.Lisse B →
    cp (Abelian.image g) ≤ f (cp A)
  signed : ∀ A, P.Lisse A → cp (P.signed A) ≤ f (cp A)
  pullback : ∀ g A, P.Lisse A → cp ((O.pullback g).obj A) ≤ f (max (cm g) (cp A))
  dualTate : ∀ A, P.Lisse A → cp (P.dualTateMinusOne A) ≤ f (cp A)
  unit : cp (𝟙_ C) ≤ unitCap
  tensor : ∀ A B, P.Lisse A → P.Lisse B → cp (A ⊗ B) ≤ f (max (cp A) (cp B))
  ic : ∀ A, P.Lisse A → SD.complexity (IC.geometric A) ≤ f (cp A)

variable (K : KloostermanInputData D) (R : CurveRules D)
  (G : CohomologyRules D H P) (O : TorusOperationData p C)
  (T : TorusArithmeticData p C) (TR : TorusRules P O T)
  (IC : IntermediateExtensionData realization C)
  (f : ℕ → ℕ) (sourceCap unitCap : ℕ) (ci : Input → ℕ) (cp : C → ℕ)
  (cm : TorusMorphismComplexity (ZMod p))
  (Q : OperationBounds (D := D) (H := H) (P := P) f unitCap ci cp cm O IC)
  (QM : TorusPolynomialRules cm)
  (hfirst : ci K.first ≤ sourceCap) (hsecond : ci K.second ≤ sourceCap)
  (hadditive : ci K.additive ≤ sourceCap)

local notation "b" => budget f (initialCap sourceCap unitCap)

include R Q hfirst hsecond hadditive in
/-- The first three steps bound the literal rank-nine input term. -/
theorem input_complexity_le : ci K.input ≤ b 3 := by
  have first : ci K.first ≤ b 0 := hfirst.trans (le_max_left _ _)
  have second : ci K.second ≤ b 0 := hsecond.trans (le_max_left _ _)
  have additive : ci K.additive ≤ b 0 := hadditive.trans (le_max_left _ _)
  have hd : ci (D.dual K.second) ≤ b 1 :=
    (Q.input_dual _ K.second_lisse).trans (operation_le_budget _ _ 0 _ second)
  have ht : ci (D.tensor K.first (D.dual K.second)) ≤ b 2 :=
    (Q.input_tensor _ _ K.first_lisse (R.dual_lisse _ K.second_lisse)).trans
      (operation_le_budget _ _ 1 _ (max_le (first.trans (budget_mono _ _ (by decide))) hd))
  exact (Q.input_tensor _ _
    (R.tensor_lisse _ _ K.first_lisse (R.dual_lisse _ K.second_lisse)) K.additive_lisse).trans
    (operation_le_budget _ _ 2 _ (max_le ht (additive.trans (budget_mono _ _ (by decide)))))

include R G Q hfirst hsecond hadditive in
/-- Compact cohomology, its actual image, then the sign line. -/
theorem signed_core_complexity_le : cp (P.signed (parabolicCore H K.input)) ≤ b 6 := by
  have hc : cp (H.compact K.input) ≤ b 4 :=
    (Q.compact _ (K.input_lisse R)).trans (operation_le_budget _ _ 3 _
      (input_complexity_le K R O IC f sourceCap unitCap ci cp cm Q hfirst hsecond hadditive))
  have hi : cp (parabolicCore H K.input) ≤ b 5 :=
    (Q.image _ _ (H.comparison K.input) (compact_lisse K R G) (ordinary_lisse K R G)).trans
      (operation_le_budget _ _ 4 _ hc)
  exact (Q.signed _ (core_lisse K R G)).trans (operation_le_budget _ _ 5 _ hi)

include R G Q QM hfirst hsecond hadditive in
/-- Apply the proved polynomial bound to the genuine physical scheme map. -/
theorem pulledEntry_complexity_le (α m n : (ZMod p)ˣ) :
    cp (pulledEntry (H := H) (P := P) K O α m n) ≤ b 7 := by
  apply (Q.pullback _ _ (signed_core_lisse K R G)).trans
  apply operation_le_budget _ _ 6
  apply max_le
  · exact (physical_complexity_le_explicit QM α m n).trans
      (((le_max_right unitCap 34646092416).trans (le_max_right sourceCap _)).trans
        (budget_mono _ _ (by decide : 0 ≤ 6)))
  · exact signed_core_complexity_le K R G O IC f sourceCap unitCap ci cp cm Q
      hfirst hsecond hadditive

include R G TR Q QM hfirst hsecond hadditive in
/-- All four actual entries, in the original cyclic orientation. -/
theorem entry_complexity_le (α m m' n n' : (ZMod p)ˣ) (i : Fin 4) :
    cp (entryObjects (H := H) (P := P) K O α m m' n n' i) ≤ b 8 := by
  have he (m n : (ZMod p)ˣ) :=
    pulledEntry_complexity_le K R G O IC f sourceCap unitCap ci cp cm Q QM
      hfirst hsecond hadditive α m n
  have hd (m n : (ZMod p)ˣ) :
      cp (P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m n)) ≤ b 8 :=
    (Q.dualTate _ (pulledEntry_lisse K R G O T TR α m n)).trans
      (operation_le_budget _ _ 7 _ (he m n))
  fin_cases i
  · exact (he m n).trans (budget_mono _ _ (by decide))
  · exact hd m' n
  · exact (he m' n').trans (budget_mono _ _ (by decide))
  · exact hd m n'

include TR Q in
/-- Each actual monoidal tensor costs one more envelope step. -/
theorem tensorList_complexity_le (V : Fin 4 → C)
    (hl : ∀ i, P.Lisse (V i)) (hv : ∀ i, cp (V i) ≤ b 8) (is : List (Fin 4)) :
    cp (tensorList V is) ≤ b (8 + is.length) := by
  induction is with
  | nil =>
      exact Q.unit.trans (((le_max_left unitCap 34646092416).trans
        (le_max_right sourceCap _)).trans (budget_mono _ _ (by decide : 0 ≤ 8)))
  | cons i is ih =>
      apply (Q.tensor _ _ (hl i) (tensorList_lisse TR V hl is)).trans
      exact operation_le_budget _ _ (8 + is.length) _
        (max_le ((hv i).trans (budget_mono _ _ (Nat.le_add_right 8 is.length))) ih)

include R G TR Q QM hfirst hsecond hadditive in
/-- One cap for every subset, with all constants independent of the five
residue parameters. The result is about the existing `physicalObjects`
term, not a replacement family with a stipulated bound. -/
theorem physical_objects_complexity_le (α m m' n n' : (ZMod p)ˣ)
    (S : Finset (Fin 4)) :
    SD.complexity (physicalObjects IC
      (entryObjects (H := H) (P := P) K O α m m' n n') S) ≤
      physicalCap f sourceCap unitCap := by
  let V := entryObjects (H := H) (P := P) K O α m m' n n'
  have hl : ∀ i, P.Lisse (V i) := entryObjects_lisse K R G O T TR α m m' n n'
  have hv : ∀ i, cp (V i) ≤ b 8 :=
    entry_complexity_le K R G O T TR IC f sourceCap unitCap ci cp cm Q QM
      hfirst hsecond hadditive α m m' n n'
  have ht : cp (tensorSubset V S) ≤ b 12 :=
    (tensorList_complexity_le O T TR IC f sourceCap unitCap ci cp cm Q V hl hv S.toList).trans
      (budget_mono _ _ (by
        rw [Finset.length_toList]
        have hc : S.card ≤ 4 := (Finset.card_le_univ S).trans_eq (by decide)
        omega))
  exact (Q.ic _ (tensorSubset_lisse TR V hl S)).trans (operation_le_budget _ _ 12 _ ht)

end PrimeGap182.TypeIII.PublishedConstructionComplexity

#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.budget_mono
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.operation_le_budget
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.input_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.signed_core_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.pulledEntry_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.entry_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.tensorList_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedConstructionComplexity.physical_objects_complexity_le
