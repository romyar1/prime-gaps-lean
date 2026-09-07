import TypeIIIFrobeniusTraceBounds
import TypeIIIScalingSupport
import Mathlib.Data.Set.Card

/-!
# Conditional translation of published perverse-support rules

This interface records observables of perverse surface objects and explicitly
assumed general BBD/QST/coefficient-transport laws. It is not a realization in
the foundational Artin--Schreier or adic code. No Type III Fourier bound,
family covariance, or constituent exclusion is assumed as a general law.

Geometric dimensions are recorded at `K × K`, with indices `0,1,2` denoting
ordinary degrees `-2,-1,0`. Frobenius blocks occur only in the separate
`RationalStalkRealization`, at prime-field rational points of a chosen Weil
lift. A geometric constituent need not have such a lift. In the intended
application `K` is an algebraic closure of the prime field.

BBD references: Corollaries 1.4.24--1.4.25, Theorem 4.3.1 and Theorem 5.3.8.
QST references: Theorem 6.15, Theorem 6.23 and Proposition 6.24. The coefficient
laws express exact equivalences commuting with stalks and intermediate
extension, not preservation of complex norms. Details and primary links are
in `research/type_iii/published_inputs/support_and_weights_audit.md`.

The proved consequences include finite ordinary degree `-1` support and
vanishing degree `0` when all geometric simple constituents have full support.
A separately supplied family coefficient/dilation isomorphism makes the
proper-support and punctual-support unions invariant. Bounded punctual support
then lies at the origin by the previously proved characteristic cutoff.
-/

noncomputable section
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.PublishedSupportRules

universe u v

/-- Observables, with no assertion that a particular sheaf realizes them.
The constituent list retains Jordan--Hölder multiplicities. -/
structure SurfaceData (K : Type u) (Obj : Type v) where
  geomDim : Obj → K × K → Fin 3 → ℕ
  support : Obj → Set (K × K)
  constituents : Obj → List Obj
  Pure : Obj → Prop
  Simple : Obj → Prop
  complexity : Obj → ℕ

namespace SurfaceData

variable {K : Type u} {Obj : Type v} (D : SurfaceData K Obj)

def ordinarySupport (Q : Obj) (i : Fin 3) : Set (K × K) :=
  {z | D.geomDim Q z i ≠ 0}

def constituentSupports (Q : Obj) : Set (Set (K × K)) :=
  D.support '' {C | C ∈ D.constituents Q}

def properSupportUnion (Q : Obj) : Set (K × K) :=
  {z | ∃ Z ∈ D.constituentSupports Q, Z ≠ Set.univ ∧ z ∈ Z}

def punctualSupportUnion (Q : Obj) : Set (K × K) :=
  {z | ({z} : Set (K × K)) ∈ D.constituentSupports Q}

def NoProperConstituents (Q : Obj) : Prop :=
  ∀ C ∈ D.constituents Q, D.support C = Set.univ

theorem mem_properSupportUnion (Q : Obj) (z : K × K) :
    z ∈ D.properSupportUnion Q ↔
      ∃ C ∈ D.constituents Q, D.support C ≠ Set.univ ∧ z ∈ D.support C := by
  constructor
  · rintro ⟨Z, ⟨C, hC, rfl⟩, hZ, hz⟩
    exact ⟨C, hC, hZ, hz⟩
  · rintro ⟨C, hC, hZ, hz⟩
    exact ⟨D.support C, ⟨C, hC, rfl⟩, hZ, hz⟩

theorem mem_punctualSupportUnion (Q : Obj) (z : K × K) :
    z ∈ D.punctualSupportUnion Q ↔
      ∃ C ∈ D.constituents Q, D.support C = {z} := Iff.rfl

theorem constituentSupports_finite (Q : Obj) :
    (D.constituentSupports Q).Finite :=
  (D.constituents Q).finite_toSet.image D.support

theorem punctualSupportUnion_finite (Q : Obj) :
    (D.punctualSupportUnion Q).Finite :=
  Set.Finite.preimage Set.singleton_injective.injOn (D.constituentSupports_finite Q)

/-- Each punctual support is a singleton support of some constituent; no
classification of positive-dimensional supports is used. -/
theorem punctualSupportUnion_ncard_le_length (Q : Obj) :
    (D.punctualSupportUnion Q).ncard ≤ (D.constituents Q).length := by
  calc
    _ ≤ (D.constituentSupports Q).ncard :=
      Set.ncard_le_ncard_of_injOn (fun z : K × K => ({z} : Set (K × K)))
        (fun _ hz => hz) Set.singleton_injective.injOn (D.constituentSupports_finite Q)
    _ ≤ {C | C ∈ D.constituents Q}.ncard :=
      Set.ncard_image_le (D.constituents Q).finite_toSet
    _ = (D.constituents Q).toFinset.card := by
      have he : {C | C ∈ D.constituents Q} =
          ((D.constituents Q).toFinset : Set Obj) := by ext; simp
      rw [he, Set.ncard_coe_finset]
    _ ≤ _ := List.toFinset_card_le (D.constituents Q)

end SurfaceData

/-- Published BBD rules. Geometric semisimplicity is used only for pure
objects; strict support is imposed only on simple full-support objects. -/
structure BBDRules {K : Type u} {Obj : Type v} (D : SurfaceData K Obj) : Prop where
  constituent_simple : ∀ Q C, C ∈ D.constituents Q → D.Simple C
  pure_dimension_decomposition : ∀ Q, D.Pure Q → ∀ z i,
    D.geomDim Q z i = ((D.constituents Q).map (fun C => D.geomDim C z i)).sum
  simple_full_minusOne_finite : ∀ C, D.Simple C → D.support C = Set.univ →
    (D.ordinarySupport C 1).Finite
  simple_full_zero : ∀ C, D.Simple C → D.support C = Set.univ →
    ∀ z, D.geomDim C z 2 = 0
  simple_zero_stalk_punctual : ∀ C, D.Simple C → ∀ z,
    D.geomDim C z 2 ≠ 0 → D.support C = {z}

/-- Generic classification of irreducible closed supports in the affine
plane over an algebraically closed field. This combines BBD's simple-support
classification with the height-one-prime classification in `K[X,Y]`.
There is no claim excluding either proper-support alternative. -/
structure SupportClassification {K : Type u} [Field K] [IsAlgClosed K]
    {Obj : Type v} (D : SurfaceData K Obj) : Prop where
  proper_simple_support : ∀ C, D.Simple C → D.support C ≠ Set.univ →
    (∃ z : K × K, D.support C = {z}) ∨
      ∃ f : MvPolynomial (Fin 2) K, Irreducible f ∧
        D.support C = {z | MvPolynomial.eval ![z.1, z.2] f = 0}

/-- Generic quantitative-sheaf bounds, separate from any exclusion or
covariance statement. The containing-polynomial bound is a consequence of
the total degree bound for the proper simple supports. -/
structure QSTRules {K : Type u} [Field K] {Obj : Type v}
    (D : SurfaceData K Obj) where
  stalkBound : ℕ → ℕ
  ordinarySupportBound : ℕ → ℕ
  constituentBound : ℕ → ℕ
  properDegreeBound : ℕ → ℕ
  geomDim_le : ∀ Q z i, D.geomDim Q z i ≤ stalkBound (D.complexity Q)
  ordinarySupport_ncard_le : ∀ Q i, (D.ordinarySupport Q i).Finite →
    (D.ordinarySupport Q i).ncard ≤ ordinarySupportBound (D.complexity Q)
  constituent_length_le : ∀ Q,
    (D.constituents Q).length ≤ constituentBound (D.complexity Q)
  properSupport_polynomial : ∀ Q, ∃ F : MvPolynomial (Fin 2) K,
    F ≠ 0 ∧ F.totalDegree ≤ properDegreeBound (D.complexity Q) ∧
      ∀ z ∈ D.properSupportUnion Q, MvPolynomial.eval ![z.1, z.2] F = 0

/-- Perverse support dimension at most one in degree `-1`, combined with
QST's ordinary-cohomology degree bounds. This permits a curve exceptional
locus and makes no assertion that it is finite. -/
structure OrdinarySupportDegreeRules {K : Type u} [Field K] {Obj : Type v}
    (D : SurfaceData K Obj) where
  degreeBound : ℕ → ℕ
  minusOne_polynomial : ∀ Q, ∃ F : MvPolynomial (Fin 2) K,
    F ≠ 0 ∧ F.totalDegree ≤ degreeBound (D.complexity Q) ∧
      ∀ z ∈ D.ordinarySupport Q 1, MvPolynomial.eval ![z.1, z.2] F = 0

variable {K : Type u} {Obj : Type v} {D : SurfaceData K Obj}

/-- Pure decomposition forces a nonzero stalk degree to occur in a simple
constituent in the same degree. -/
theorem ordinarySupport_subset_constituents (B : BBDRules D)
    (Q : Obj) (hQ : D.Pure Q) (i : Fin 3) :
    D.ordinarySupport Q i ⊆
      ⋃ C ∈ {C | C ∈ D.constituents Q}, D.ordinarySupport C i := by
  intro z hz
  change D.geomDim Q z i ≠ 0 at hz
  by_contra h
  have hdim : ∀ C ∈ D.constituents Q, D.geomDim C z i = 0 := by
    intro C hC
    by_contra hn
    apply h
    exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC, hn⟩⟩
  apply hz
  rw [B.pure_dimension_decomposition Q hQ z i]
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hn
  exact hdim C hC

/-- Pure dimension decomposition and the generic simple-support rule
place ordinary degree `0` support in the punctual constituent union. -/
theorem zero_support_subset_punctualSupportUnion (B : BBDRules D)
    (Q : Obj) (hQ : D.Pure Q) :
    D.ordinarySupport Q 2 ⊆ D.punctualSupportUnion Q := by
  intro z hz
  have h := ordinarySupport_subset_constituents B Q hQ 2 hz
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp h
  obtain ⟨hmem, hdim⟩ := Set.mem_iUnion.mp hC
  apply (D.mem_punctualSupportUnion Q z).mpr
  exact ⟨C, hmem,
    B.simple_zero_stalk_punctual C (B.constituent_simple Q C hmem) z hdim⟩

/-- The finite degree `-1` locus is a derived consequence of full support
of every simple constituent, not an assumed conclusion for `Q`. -/
theorem minusOne_support_finite_of_no_proper_constituents (B : BBDRules D)
    (Q : Obj) (hQ : D.Pure Q) (hfull : D.NoProperConstituents Q) :
    (D.ordinarySupport Q 1).Finite := by
  have hfinite : (⋃ C ∈ {C | C ∈ D.constituents Q}, D.ordinarySupport C 1).Finite :=
    (D.constituents Q).finite_toSet.biUnion fun C hC =>
      B.simple_full_minusOne_finite C (B.constituent_simple Q C hC) (hfull C hC)
  exact hfinite.subset (ordinarySupport_subset_constituents B Q hQ 1)

theorem zero_dimension_eq_zero_of_no_proper_constituents (B : BBDRules D)
    (Q : Obj) (hQ : D.Pure Q) (hfull : D.NoProperConstituents Q) (z : K × K) :
    D.geomDim Q z 2 = 0 := by
  rw [B.pure_dimension_decomposition Q hQ z 2]
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hn
  exact B.simple_full_zero C (B.constituent_simple Q C hC) (hfull C hC) z

/-- A geometric exceptional set with an explicit generic complexity bound.
Transport to prime-field points is a separate, injective point-map argument. -/
theorem exists_bounded_minusOne_support_of_no_proper_constituents [Field K]
    (B : BBDRules D) (C : QSTRules D) (Q : Obj) (hQ : D.Pure Q)
    (hfull : D.NoProperConstituents Q) :
    ∃ Z : Finset (K × K), Z.card ≤ C.ordinarySupportBound (D.complexity Q) ∧
      (∀ z, z ∈ Z ↔ D.geomDim Q z 1 ≠ 0) ∧
      (∀ z, z ∉ Z → D.geomDim Q z 1 = 0) ∧
      (∀ z, D.geomDim Q z 2 = 0) := by
  have hfinite := minusOne_support_finite_of_no_proper_constituents B Q hQ hfull
  refine ⟨hfinite.toFinset, ?_, ?_, ?_,
    zero_dimension_eq_zero_of_no_proper_constituents B Q hQ hfull⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfinite]
    exact C.ordinarySupport_ncard_le Q 1 hfinite
  · intro z
    exact hfinite.mem_toFinset
  · intro z hz
    by_contra hn
    exact hz (hfinite.mem_toFinset.mpr hn)

/-- Actual dilation of the geometric plane by a unit. -/
def planeDilation [Field K] (a : Kˣ) : (K × K) ≃ (K × K) where
  toFun z := ((a : K) * z.1, (a : K) * z.2)
  invFun z := (((a⁻¹ : Kˣ) : K) * z.1, ((a⁻¹ : Kˣ) : K) * z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

@[simp] theorem planeDilation_apply [Field K] (a : Kˣ) (z : K × K) :
    planeDilation a z = ((a : K) * z.1, (a : K) * z.2) := rfl

/-- Conditional translation of coefficient and pullback equivalence laws.
There is deliberately no family covariance field and no norm-preservation law. -/
structure CoefficientTransport [Field K] (D : SurfaceData K Obj) where
  Isomorphic : Obj → Obj → Prop
  coefficient : Obj → Obj
  dilate : Kˣ → Obj → Obj
  supports_isomorphic : ∀ {Q R}, Isomorphic Q R →
    D.constituentSupports Q = D.constituentSupports R
  supports_coefficient : ∀ Q,
    D.constituentSupports (coefficient Q) = D.constituentSupports Q
  supports_dilate : ∀ a Q,
    D.constituentSupports (dilate a Q) =
      (fun Z : Set (K × K) => (planeDilation a) ⁻¹' Z) '' D.constituentSupports Q
  geomDim_isomorphic : ∀ {Q R}, Isomorphic Q R → ∀ z i,
    D.geomDim Q z i = D.geomDim R z i
  geomDim_coefficient : ∀ Q z i, D.geomDim (coefficient Q) z i = D.geomDim Q z i
  geomDim_dilate : ∀ a Q z i,
    D.geomDim (dilate a Q) z i = D.geomDim Q (planeDilation a z) i

variable [Field K]

/-- The isomorphism in this statement is a separate, family-specific proof
obligation. Only its formal consequence for support collections is derived. -/
theorem constituentSupports_eq_preimage_image_of_covariance
    (T : CoefficientTransport D) (Q : Obj) (a : Kˣ)
    (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q)) :
    D.constituentSupports Q =
      (fun Z : Set (K × K) => (planeDilation a) ⁻¹' Z) '' D.constituentSupports Q := by
  calc
    _ = D.constituentSupports (T.coefficient Q) := (T.supports_coefficient Q).symm
    _ = D.constituentSupports (T.dilate a Q) := T.supports_isomorphic hcov
    _ = _ := T.supports_dilate a Q

theorem geomDim_eq_dilate_of_covariance (T : CoefficientTransport D)
    (Q : Obj) (a : Kˣ) (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q))
    (z : K × K) (i : Fin 3) :
    D.geomDim Q z i = D.geomDim Q (planeDilation a z) i := by
  calc
    _ = D.geomDim (T.coefficient Q) z i := (T.geomDim_coefficient Q z i).symm
    _ = D.geomDim (T.dilate a Q) z i := T.geomDim_isomorphic hcov z i
    _ = _ := T.geomDim_dilate a Q z i

theorem ordinarySupport_invariant_of_covariance (T : CoefficientTransport D)
    (Q : Obj) (a : Kˣ) (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q))
    (i : Fin 3) :
    ∀ z ∈ D.ordinarySupport Q i, planeDilation a z ∈ D.ordinarySupport Q i := by
  intro z hz
  change D.geomDim Q (planeDilation a z) i ≠ 0
  rw [← geomDim_eq_dilate_of_covariance T Q a hcov z i]
  exact hz

/-- The union is invariant even when coefficient change permutes the
individual proper simple supports. -/
theorem properSupportUnion_invariant_of_covariance (T : CoefficientTransport D)
    (Q : Obj) (a : Kˣ) (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q)) :
    ∀ z ∈ D.properSupportUnion Q, planeDilation a z ∈ D.properSupportUnion Q := by
  intro z hz
  obtain ⟨Z, hZ, hproper, hzZ⟩ := hz
  rw [constituentSupports_eq_preimage_image_of_covariance T Q a hcov] at hZ
  obtain ⟨W, hW, hpre⟩ := hZ
  change (planeDilation a) ⁻¹' W = Z at hpre
  refine ⟨W, hW, ?_, ?_⟩
  · intro hWu
    apply hproper
    rw [← hpre, hWu]
    exact Set.preimage_univ
  · change z ∈ (planeDilation a) ⁻¹' W
    rwa [hpre]

theorem punctualSupportUnion_invariant_of_covariance (T : CoefficientTransport D)
    (Q : Obj) (a : Kˣ) (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q)) :
    ∀ z ∈ D.punctualSupportUnion Q, planeDilation a z ∈ D.punctualSupportUnion Q := by
  intro z hz
  change ({z} : Set (K × K)) ∈ D.constituentSupports Q at hz
  rw [constituentSupports_eq_preimage_image_of_covariance T Q a hcov] at hz
  obtain ⟨W, hW, hpre⟩ := hz
  change (planeDilation a) ⁻¹' W = {z} at hpre
  have he : W = {planeDilation a z} := by
    ext w
    constructor
    · intro hw
      have hw' : (planeDilation a).symm w ∈ (planeDilation a) ⁻¹' W := by
        simpa using hw
      rw [hpre] at hw'
      change (planeDilation a).symm w = z at hw'
      change w = planeDilation a z
      rw [← hw', Equiv.apply_symm_apply]
    · intro hw
      change w = planeDilation a z at hw
      subst w
      change z ∈ (planeDilation a) ⁻¹' W
      rw [hpre]
      exact Set.mem_singleton z
  change ({planeDilation a z} : Set (K × K)) ∈ D.constituentSupports Q
  rwa [← he]

theorem punctualSupportUnion_ncard_le (C : QSTRules D) (Q : Obj) :
    (D.punctualSupportUnion Q).ncard ≤ C.constituentBound (D.complexity Q) :=
  (D.punctualSupportUnion_ncard_le_length Q).trans (C.constituent_length_le Q)

/-- A bounded coefficient-invariant punctual union consists only of the
origin. The bound and covariance have distinct, explicitly supplied sources. -/
theorem punctual_union_subset_origin_of_covariance {p : ℕ} [CharP K p]
    (C : QSTRules D) (T : CoefficientTransport D) (Q : Obj) (a : Kˣ)
    (ha : (a : K) = 8) (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q))
    (hp : 8 ^ C.constituentBound (D.complexity Q) < p) :
    D.punctualSupportUnion Q ⊆ {(0, 0)} := by
  have hf := D.punctualSupportUnion_finite Q
  have hcard : hf.toFinset.card ≤ C.constituentBound (D.complexity Q) := by
    rw [← Set.ncard_eq_toFinset_card _ hf]
    exact punctualSupportUnion_ncard_le C Q
  have hscale : ∀ z ∈ hf.toFinset, ((8 : K) * z.1, (8 : K) * z.2) ∈ hf.toFinset := by
    intro z hz
    apply hf.mem_toFinset.mpr
    have h := punctualSupportUnion_invariant_of_covariance T Q a hcov z
      (hf.mem_toFinset.mp hz)
    simpa only [planeDilation_apply, ha] using h
  intro z hz
  exact ScalingSupport.eight_invariant_finite_support _ hp hf.toFinset hcard hscale z
    (hf.mem_toFinset.mpr hz)

/-- Degree `0` is supported at the origin under covariance, even when
proper curve constituents are allowed. -/
theorem zero_support_subset_origin_of_covariance {p : ℕ} [CharP K p]
    (B : BBDRules D) (C : QSTRules D) (T : CoefficientTransport D)
    (Q : Obj) (hQ : D.Pure Q) (a : Kˣ) (ha : (a : K) = 8)
    (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q))
    (hp : 8 ^ C.constituentBound (D.complexity Q) < p) :
    D.ordinarySupport Q 2 ⊆ {(0, 0)} :=
  (zero_support_subset_punctualSupportUnion B Q hQ).trans
    (punctual_union_subset_origin_of_covariance C T Q a ha hcov hp)

/-- After full-support exclusion, the same geometric covariance also
places the finite ordinary degree `-1` support at the origin. -/
theorem minusOne_support_subset_origin_of_covariance {p : ℕ} [CharP K p]
    (B : BBDRules D) (C : QSTRules D) (T : CoefficientTransport D)
    (Q : Obj) (hQ : D.Pure Q) (hfull : D.NoProperConstituents Q) (a : Kˣ)
    (ha : (a : K) = 8) (hcov : T.Isomorphic (T.coefficient Q) (T.dilate a Q))
    (hp : 8 ^ C.ordinarySupportBound (D.complexity Q) < p) :
    D.ordinarySupport Q 1 ⊆ {(0, 0)} := by
  have hf := minusOne_support_finite_of_no_proper_constituents B Q hQ hfull
  have hcard : hf.toFinset.card ≤ C.ordinarySupportBound (D.complexity Q) := by
    rw [← Set.ncard_eq_toFinset_card _ hf]
    exact C.ordinarySupport_ncard_le Q 1 hf
  have hscale : ∀ z ∈ hf.toFinset, ((8 : K) * z.1, (8 : K) * z.2) ∈ hf.toFinset := by
    intro z hz
    apply hf.mem_toFinset.mpr
    have h := ordinarySupport_invariant_of_covariance T Q a hcov 1 z
      (hf.mem_toFinset.mp hz)
    simpa only [planeDilation_apply, ha] using h
  intro z hz
  exact ScalingSupport.eight_invariant_finite_support _ hp hf.toFinset hcard hscale z
    (hf.mem_toFinset.mpr hz)

/-- Frobenius data for a chosen arithmetic lift of a geometric object.
`WeilLift Q` may be empty: a geometric simple constituent need not descend
to the prime field. No Frobenius action is assigned to it merely because
it occurs in a geometric decomposition. Only dimensions are compared here;
the record supplies neither a trace identity nor any eigenvalue estimate. -/
structure RationalStalkRealization (p : ℕ) [Algebra (ZMod p) K]
    (D : SurfaceData K Obj) where
  WeilLift : Obj → Type v
  stalk : {Q : Obj} → WeilLift Q → ZMod p → ZMod p → SurfaceStalk
  minusTwo_dimension : ∀ {Q} (W : WeilLift Q) x y, (stalk W x y).minusTwo.dimension =
    D.geomDim Q (algebraMap (ZMod p) K x, algebraMap (ZMod p) K y) 0
  minusOne_dimension : ∀ {Q} (W : WeilLift Q) x y, (stalk W x y).minusOne.dimension =
    D.geomDim Q (algebraMap (ZMod p) K x, algebraMap (ZMod p) K y) 1
  zero_dimension : ∀ {Q} (W : WeilLift Q) x y, (stalk W x y).zero.dimension =
    D.geomDim Q (algebraMap (ZMod p) K x, algebraMap (ZMod p) K y) 2

#print axioms SurfaceData
#print axioms SurfaceData.mk
#print axioms SurfaceData.geomDim
#print axioms SurfaceData.support
#print axioms SurfaceData.constituents
#print axioms SurfaceData.Pure
#print axioms SurfaceData.Simple
#print axioms SurfaceData.complexity
#print axioms SurfaceData.ordinarySupport
#print axioms SurfaceData.constituentSupports
#print axioms SurfaceData.properSupportUnion
#print axioms SurfaceData.punctualSupportUnion
#print axioms SurfaceData.NoProperConstituents
#print axioms SurfaceData.mem_properSupportUnion
#print axioms SurfaceData.mem_punctualSupportUnion
#print axioms SurfaceData.constituentSupports_finite
#print axioms SurfaceData.punctualSupportUnion_finite
#print axioms SurfaceData.punctualSupportUnion_ncard_le_length
#print axioms BBDRules
#print axioms BBDRules.mk
#print axioms BBDRules.constituent_simple
#print axioms BBDRules.pure_dimension_decomposition
#print axioms BBDRules.simple_full_minusOne_finite
#print axioms BBDRules.simple_full_zero
#print axioms BBDRules.simple_zero_stalk_punctual
#print axioms SupportClassification
#print axioms SupportClassification.mk
#print axioms SupportClassification.proper_simple_support
#print axioms QSTRules
#print axioms QSTRules.mk
#print axioms QSTRules.stalkBound
#print axioms QSTRules.ordinarySupportBound
#print axioms QSTRules.constituentBound
#print axioms QSTRules.properDegreeBound
#print axioms QSTRules.geomDim_le
#print axioms QSTRules.ordinarySupport_ncard_le
#print axioms QSTRules.constituent_length_le
#print axioms QSTRules.properSupport_polynomial
#print axioms OrdinarySupportDegreeRules
#print axioms OrdinarySupportDegreeRules.mk
#print axioms OrdinarySupportDegreeRules.degreeBound
#print axioms OrdinarySupportDegreeRules.minusOne_polynomial
#print axioms ordinarySupport_subset_constituents
#print axioms zero_support_subset_punctualSupportUnion
#print axioms minusOne_support_finite_of_no_proper_constituents
#print axioms zero_dimension_eq_zero_of_no_proper_constituents
#print axioms exists_bounded_minusOne_support_of_no_proper_constituents
#print axioms planeDilation
#print axioms planeDilation_apply
#print axioms CoefficientTransport
#print axioms CoefficientTransport.mk
#print axioms CoefficientTransport.Isomorphic
#print axioms CoefficientTransport.coefficient
#print axioms CoefficientTransport.dilate
#print axioms CoefficientTransport.supports_isomorphic
#print axioms CoefficientTransport.supports_coefficient
#print axioms CoefficientTransport.supports_dilate
#print axioms CoefficientTransport.geomDim_isomorphic
#print axioms CoefficientTransport.geomDim_coefficient
#print axioms CoefficientTransport.geomDim_dilate
#print axioms constituentSupports_eq_preimage_image_of_covariance
#print axioms geomDim_eq_dilate_of_covariance
#print axioms ordinarySupport_invariant_of_covariance
#print axioms properSupportUnion_invariant_of_covariance
#print axioms punctualSupportUnion_invariant_of_covariance
#print axioms punctualSupportUnion_ncard_le
#print axioms punctual_union_subset_origin_of_covariance
#print axioms zero_support_subset_origin_of_covariance
#print axioms minusOne_support_subset_origin_of_covariance
#print axioms RationalStalkRealization
#print axioms RationalStalkRealization.mk
#print axioms RationalStalkRealization.WeilLift
#print axioms RationalStalkRealization.stalk
#print axioms RationalStalkRealization.minusTwo_dimension
#print axioms RationalStalkRealization.minusOne_dimension
#print axioms RationalStalkRealization.zero_dimension

end PrimeGap182.TypeIII.PublishedSupportRules
