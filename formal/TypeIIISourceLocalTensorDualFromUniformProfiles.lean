import TypeIIIUniformSourceLocalObservablesFromParameterFibers

/-!
# Source local tensor/dual rules from uniform actual-fiber break profiles

Katz GKM 1.3 gives tensor-component breaks: unequal input breaks give their
maximum, while equal breaks can only decrease. GKM 1.5 preserves the actual
multiplicity profile under contragredient duality. These precisely universal
local comparisons concern ALL globally-lisse Gm objects over ALL fields, not
selected Type III source laws. SAME-U inverse images and SAME-origin monoidal
realizations transport them to every actual source parameter fiber.

The finite-locally-free internal-Hom inverse-image comparison is explicit
for ALL schemes/morphisms/globally-lisse objects. Actual continuous adic/local
upper-break realization and that general published-to-model match remain
external. No chosen source local predicate or completed source rules is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.SourceLocalTensorDualFromUniformProfiles
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open UniformSourceLocalObservablesFromParameterFibers QSTDualityBridgesFromSmoothLisseVerdier

/-- A break in a tensor comes from a pair of input breaks. Unequal breaks
force their maximum; equal breaks may decrease. This is the finite-support
consequence of the general break-decomposition theorem, GKM 1.3. -/
def TensorBreakPairs (a b c : BreakProfile) : Prop :=
  ∀ t ∈ c.multiplicity.support, ∃ r ∈ a.multiplicity.support,
    ∃ s ∈ b.multiplicity.support, t ≤ max r s ∧ (r ≠ s → t = max r s)

/-- The pair theorem propagates a common bound without positive-rank premises. -/
theorem tensorBreakPairs_bounded (a b c : BreakProfile) (h : TensorBreakPairs a b c)
    (s : ℚ) (ha : ∀ r ∈ a.multiplicity.support, r ≤ s)
    (hb : ∀ r ∈ b.multiplicity.support, r ≤ s) :
    ∀ t ∈ c.multiplicity.support, t ≤ s := by
  intro t ht
  obtain ⟨r, hr, q, hq, htq, _⟩ := h t ht
  exact htq.trans (max_le (ha r hr) (hb q hq))

/-- An unequal bounded/isoclinic pair forces the larger slope on the tensor. -/
theorem tensorBreakPairs_unequal (a b c : BreakProfile) (h : TensorBreakPairs a b c)
    (r s : ℚ) (hrs : r < s) (ha : ∀ q ∈ a.multiplicity.support, q ≤ r)
    (hb : ∀ q ∈ b.multiplicity.support, q = s) :
    ∀ t ∈ c.multiplicity.support, t = s := by
  intro t ht
  obtain ⟨q, hq, v, hv, _, he⟩ := h t ht
  have hqs : q < s := lt_of_le_of_lt (ha q hq) hrs
  have hv' : v = s := hb v hv
  subst v
  exact (he (ne_of_lt hqs)).trans (max_eq_right (le_of_lt hqs))

/-- Trivial wild actions remain trivial under the actual tensor action. -/
theorem wildTrivial_tensor {H : Type} [Group H] (P : Subgroup H)
    (V W : FDRep (PadicAlgCl 2) H) (hV : wildTrivial P V) (hW : wildTrivial P W) :
    wildTrivial P (V ⊗ W) := by
  intro g
  change TensorProduct.map (V.ρ g.val) (W.ρ g.val) = LinearMap.id
  rw [hV g, hW g]
  exact TensorProduct.map_id

/-- Contragredient wild triviality follows from the inverse-group action. -/
theorem wildTrivial_dual {H : Type} [Group H] (P : Subgroup H)
    (V : FDRep (PadicAlgCl 2) H) (hV : wildTrivial P V) :
    wildTrivial P (FDRep.of (Representation.dual V.ρ)) := by
  intro g
  change Module.Dual.transpose (R := PadicAlgCl 2) (V.ρ g.val⁻¹) = LinearMap.id
  have hi : V.ρ g.val⁻¹ = 1 := by simpa only [Subgroup.coe_inv] using hV g⁻¹
  rw [hi]
  rfl

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  [∀ X, MonoidalCategory (C X)] [∀ X, MonoidalClosed (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : LocalRealization C)
  [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (lisseTensor : ∀ X (A B : C X), L X A → L X B → L X (A ⊗ B))
  (lisseDual : ∀ X (A : C X), L X A → L X ((ordinaryDual C X).obj (Opposite.op A)))
  (lisseDualPullback : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A →
    ((U.pull f).obj ((ordinaryDual C Y).obj (Opposite.op A)) ≅
      (ordinaryDual C X).obj (Opposite.op ((U.pull f).obj A))))
  (localTensorPairs : ∀ (E : Type) [Field E] (_h2 : (2 : E) ≠ 0) (A B : C (ArithmeticSourceMaps.fiberScheme E)),
    L (ArithmeticSourceMaps.fiberScheme E) A → L (ArithmeticSourceMaps.fiberScheme E) B →
      TensorBreakPairs (M.profile E A) (M.profile E B) (M.profile E (A ⊗ B)))
  (localDualProfile : ∀ (E : Type) [Field E] (_h2 : (2 : E) ≠ 0) (A : C (ArithmeticSourceMaps.fiberScheme E)),
    L (ArithmeticSourceMaps.fiberScheme E) A →
      (M.profile E ((ordinaryDual C _).obj (Opposite.op A))).multiplicity =
        (M.profile E A).multiplicity)
  (localOriginDual : ∀ (E : Type) [Field E] (A : C (ArithmeticSourceMaps.fiberScheme E)),
    L (ArithmeticSourceMaps.fiberScheme E) A →
      ((M.origin E).obj ((ordinaryDual C _).obj (Opposite.op A)) ≅
        FDRep.of (Representation.dual ((M.origin E).obj A).ρ)))
  (K : Type) [Field K]
  (h2 : (2 : K) ≠ 0)

include h2 in
/-- Coefficient extensions preserve the prime-to-two domain of the local theorem. -/
theorem parameter_two_ne_zero (t : ParameterPoint K) : (2 : t.coefficientField) ≠ 0 := by
  have hi := (algebraMap K t.coefficientField).injective.ne h2
  simpa only [map_ofNat, map_zero] using hi

omit [∀ X, MonoidalClosed (C X)] in
include lisseTensor in
/-- Exact original source tensor-tame rule on EVERY actual parameter fiber. -/
theorem tensor_tame (A B : C (StartingSourceMaps.sourceScheme K))
    (hA : sourceTameZero K C U L M A) (hB : sourceTameZero K C U L M B) :
    sourceTameZero K C U L M (A ⊗ B) := by
  refine ⟨lisseTensor _ A B hA.1 hB.1, ?_⟩
  intro t
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  apply wildTrivial_iso _
    ((Functor.Monoidal.μIso (M.origin t.coefficientField) ((U.pull f).obj A) ((U.pull f).obj B)) ≪≫
      (M.origin t.coefficientField).mapIso ((Functor.Monoidal.μIso (U.pull f) A B)))
  exact wildTrivial_tensor _ _ _ (hA.2 t) (hB.2 t)

omit [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include lissePull lisseDual lisseDualPullback localOriginDual in
/-- Exact source dual-tame rule uses the finite-free dual/pullback comparison. -/
theorem dual_tame (A : C (StartingSourceMaps.sourceScheme K))
    (hA : sourceTameZero K C U L M A) :
    sourceTameZero K C U L M ((ordinaryDual C _).obj (Opposite.op A)) := by
  refine ⟨lisseDual _ A hA.1, ?_⟩
  intro t
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  let e := (M.origin t.coefficientField).mapIso (lisseDualPullback f A hA.1) ≪≫
    localOriginDual t.coefficientField ((U.pull f).obj A) (lissePull f A hA.1)
  apply wildTrivial_iso _ e.symm
  exact wildTrivial_dual _ _ (hA.2 t)

omit [∀ X, MonoidalClosed (C X)] [∀ (E : Type) [Field E], (M.origin E).Monoidal] in
include h2 lissePull lisseTensor localTensorPairs in
/-- Common source break bounds propagate through actual SAME-U tensor images. -/
theorem tensor_breaks (A B : C (StartingSourceMaps.sourceScheme K)) (s : ℚ)
    (hA : sourceBreaksLE K C U L M A s) (hB : sourceBreaksLE K C U L M B s) :
    sourceBreaksLE K C U L M (A ⊗ B) s := by
  refine ⟨lisseTensor _ A B hA.1 hB.1, ?_⟩
  intro t
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  have he := M.profile_localIso t.coefficientField _ _
    ((M.infinity t.coefficientField).mapIso ((Functor.Monoidal.μIso (U.pull f) A B)))
  change ∀ r ∈ (M.profile t.coefficientField ((U.pull f).obj (A ⊗ B))).multiplicity.support, r ≤ s
  rw [← he]
  exact tensorBreakPairs_bounded _ _ _
    (localTensorPairs t.coefficientField (parameter_two_ne_zero K h2 t) _ _ (lissePull f A hA.1) (lissePull f B hB.1))
      s (hA.2 t) (hB.2 t)

omit [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include h2 lissePull lisseDual lisseDualPullback localDualProfile in
/-- Contragredient profiles preserve the source break bound at every fiber. -/
theorem dual_breaks (A : C (StartingSourceMaps.sourceScheme K)) (s : ℚ)
    (hA : sourceBreaksLE K C U L M A s) :
    sourceBreaksLE K C U L M ((ordinaryDual C _).obj (Opposite.op A)) s := by
  refine ⟨lisseDual _ A hA.1, ?_⟩
  intro t
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  have he := M.profile_localIso t.coefficientField _ _
    ((M.infinity t.coefficientField).mapIso (lisseDualPullback f A hA.1))
  change ∀ r ∈ (M.profile t.coefficientField
    ((U.pull f).obj ((ordinaryDual C _).obj (Opposite.op A)))).multiplicity.support, r ≤ s
  rw [he, localDualProfile t.coefficientField (parameter_two_ne_zero K h2 t) _ (lissePull f A hA.1)]
  exact hA.2 t

omit [∀ X, MonoidalClosed (C X)] [∀ (E : Type) [Field E], (M.origin E).Monoidal] in
include h2 lissePull lisseTensor localTensorPairs in
/-- The exact unequal source tensor-break rule follows from GKM's pair theorem. -/
theorem tensor_unequal_breaks (A B : C (StartingSourceMaps.sourceScheme K)) (r s : ℚ)
    (hrs : r < s) (hA : sourceBreaksLE K C U L M A r) (hB : sourceIsoclinic K C U L M B s) :
    sourceIsoclinic K C U L M (A ⊗ B) s := by
  refine ⟨lisseTensor _ A B hA.1 hB.1, ?_⟩
  intro t
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  have he := M.profile_localIso t.coefficientField _ _
    ((M.infinity t.coefficientField).mapIso ((Functor.Monoidal.μIso (U.pull f) A B)))
  change ∀ q ∈ (M.profile t.coefficientField ((U.pull f).obj (A ⊗ B))).multiplicity.support, q = s
  rw [← he]
  exact tensorBreakPairs_unequal _ _ _
    (localTensorPairs t.coefficientField (parameter_two_ne_zero K h2 t) _ _ (lissePull f A hA.1) (lissePull f B hB.1))
      r s hrs (hA.2 t) (hB.2 t)

omit [∀ (E : Type) [Field E], (M.origin E).Monoidal]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include h2 lissePull lisseDual lisseDualPullback localDualProfile in
/-- Actual contragredient profiles preserve the source isoclinic slope. -/
theorem dual_isoclinic (A : C (StartingSourceMaps.sourceScheme K)) (s : ℚ)
    (hA : sourceIsoclinic K C U L M A s) :
    sourceIsoclinic K C U L M ((ordinaryDual C _).obj (Opposite.op A)) s := by
  refine ⟨lisseDual _ A hA.1, ?_⟩
  intro t
  let f := ArithmeticSourceMaps.specializationMorphism K t.coefficientField t.lambda t.xi
  have he := M.profile_localIso t.coefficientField _ _
    ((M.infinity t.coefficientField).mapIso (lisseDualPullback f A hA.1))
  change ∀ r ∈ (M.profile t.coefficientField
    ((U.pull f).obj ((ordinaryDual C _).obj (Opposite.op A)))).multiplicity.support, r = s
  rw [he, localDualProfile t.coefficientField (parameter_two_ne_zero K h2 t) _ (lissePull f A hA.1)]
  exact hA.2 t

end PrimeGap182.TypeIII.SourceLocalTensorDualFromUniformProfiles
