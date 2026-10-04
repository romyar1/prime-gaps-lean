import TypeIIIArithmeticPrimitivesFromCommonKatzConstruction
import TypeIIISourceGlobalLissityFromKatzPullbacks
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Computed primitive ramification from the general Katz local theorems

The local coefficient realization and its genuine upper-break decomposition
remain explicit general model data. The three local predicates below are
defined from that realization, rather than supplied as arbitrary predicates.
The general Katz hypotheses concern every finite field, every nontrivial
additive character and every positive raw Kloosterman rank. Tate invariance
is an isomorphism of the same local representation functors for every integer.

A finite nonnegative break decomposition with integral positive-component
Swan contributions, Swan one and no tame component has its only break at
the reciprocal of its dimension. Rank one and Swan one also imply break one,
without a separate total-wildness assumption. These are finite arithmetic
proofs; no continuous-inertia, sheaf or adic realization is constructed here.
Comparison with any independently chosen original local predicates remains
a separate conditional model interpretation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators

namespace PrimeGap182.TypeIII.PrimitiveRamificationFromGeneralKatzTheory
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open SourceGlobalLissityFromKatzPullbacks

/-- Finite upper breaks, with the general integrality of each break-component's
Swan conductor. Its interpretation as a local representation's decomposition
is an explicit part of the local realization, not supplied by this record. -/
structure BreakProfile where
  multiplicity : ℚ →₀ ℕ
  nonnegative : ∀ r ∈ multiplicity.support, 0 ≤ r
  integral : ∀ r ∈ multiplicity.support,
    ∃ m : ℕ, (m : ℚ) = r * (multiplicity r : ℚ)

def BreakProfile.rank (b : BreakProfile) : ℕ :=
  ∑ r ∈ b.multiplicity.support, b.multiplicity r

def BreakProfile.swan (b : BreakProfile) : ℚ :=
  ∑ r ∈ b.multiplicity.support, r * (b.multiplicity r : ℚ)

/-- The finite support cannot be empty if its total dimension is positive. -/
theorem BreakProfile.support_nonempty (b : BreakProfile) (h : 0 < b.rank) :
    b.multiplicity.support.Nonempty := by
  by_contra hn
  have hs : b.multiplicity.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [BreakProfile.rank, hs, Finset.sum_empty] at h
  omega

/-- Each positive break component contributes a positive integer to Swan. -/
theorem BreakProfile.positive_component (b : BreakProfile)
    (ht : b.multiplicity 0 = 0) (r : ℚ) (hr : r ∈ b.multiplicity.support) :
    1 ≤ r * (b.multiplicity r : ℚ) := by
  have hne : r ≠ 0 := by
    intro he
    exact (Finsupp.mem_support_iff.mp hr) (he ▸ ht)
  have hp : 0 < r := lt_of_le_of_ne (b.nonnegative r hr) (Ne.symm hne)
  have hm : 0 < b.multiplicity r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  obtain ⟨m, he⟩ := b.integral r hr
  have hpos : (0 : ℚ) < m := by rw [he]; exact mul_pos hp (Nat.cast_pos.mpr hm)
  have hone : 1 ≤ m := by exact Nat.succ_le_of_lt (Nat.cast_pos.mp hpos)
  rw [← he]
  exact_mod_cast hone

/-- The Swan-one argument on the finite break decomposition. -/
theorem BreakProfile.support_of_totallyWild_swan_one (b : BreakProfile)
    (n : ℕ) (hn : 0 < n) (hd : b.rank = n)
    (ht : b.multiplicity 0 = 0) (hs : b.swan = 1) :
    b.multiplicity.support = {1 / (n : ℚ)} := by
  have hc : (b.multiplicity.support.card : ℚ) ≤ 1 := by
    calc
      _ = ∑ _r ∈ b.multiplicity.support, (1 : ℚ) := by simp
      _ ≤ ∑ r ∈ b.multiplicity.support, r * (b.multiplicity r : ℚ) :=
        Finset.sum_le_sum (fun r hr => b.positive_component ht r hr)
      _ = 1 := hs
  have hc' : b.multiplicity.support.card ≤ 1 := by exact_mod_cast hc
  have hc1 : b.multiplicity.support.card = 1 :=
    Nat.le_antisymm hc' (Finset.card_pos.mpr (b.support_nonempty (hd ▸ hn)))
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc1
  have hm : b.multiplicity r = n := by simpa only [BreakProfile.rank, hr,
    Finset.sum_singleton] using hd
  have he : r * (n : ℚ) = 1 := by simpa only [BreakProfile.swan, hr,
    Finset.sum_singleton, hm] using hs
  have hnn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he' : r = 1 / (n : ℚ) := (eq_div_iff hnn).mpr he
  simpa only [he'] using hr

/-- In dimension one, Swan one already excludes a tame summand. -/
theorem BreakProfile.support_of_rank_one_swan_one (b : BreakProfile)
    (hd : b.rank = 1) (hs : b.swan = 1) :
    b.multiplicity.support = {1} := by
  have hc : b.multiplicity.support.card ≤ 1 := by
    calc
      _ = ∑ _r ∈ b.multiplicity.support, 1 := by simp
      _ ≤ ∑ r ∈ b.multiplicity.support, b.multiplicity r :=
        Finset.sum_le_sum (fun r hr => Nat.one_le_iff_ne_zero.mpr
          (Finsupp.mem_support_iff.mp hr))
      _ = 1 := hd
  have hc1 : b.multiplicity.support.card = 1 :=
    Nat.le_antisymm hc (Finset.card_pos.mpr (b.support_nonempty (by rw [hd]; omega)))
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc1
  have hm : b.multiplicity r = 1 := by simpa only [BreakProfile.rank, hr,
    Finset.sum_singleton] using hd
  have he : r = 1 := by simpa only [BreakProfile.swan, hr,
    Finset.sum_singleton, hm, Nat.cast_one, mul_one] using hs
  simpa only [he] using hr

/-- Triviality on a fixed wild inertia subgroup is an actual representation
condition. It is not a chosen sheaf predicate. -/
def wildTrivial {G : Type} [Group G] (P : Subgroup G)
    (V : FDRep (PadicAlgCl 2) G) : Prop := ∀ g : P, V.ρ g.val = 1

theorem wildTrivial_iso {G : Type} [Group G] (P : Subgroup G)
    {V W : FDRep (PadicAlgCl 2) G} (e : V ≅ W) (h : wildTrivial P V) :
    wildTrivial P W := by
  intro g
  rw [FDRep.Iso.conj_ρ e g.val, h g]
  apply LinearMap.ext
  intro v
  change (FDRep.isoToLinearEquiv e) ((FDRep.isoToLinearEquiv e).symm v) = v
  exact (FDRep.isoToLinearEquiv e).apply_symm_apply v

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)]
  [∀ X, Abelian (C X)]

/-- Local representations and upper breaks of their finite constructible
coefficient realization. Actual inertia, continuity, finite-coefficient
descent and the break-decomposition meaning are explicit external model data.
Breaks are only assigned to objects of the same ordinary system; no theorem
is asserted for arbitrary noncontinuous representations of an abstract group. -/
structure LocalRealization where
  originGroup : ∀ (K : Type) [Field K], Type
  infinityGroup : ∀ (K : Type) [Field K], Type
  originGroupStructure : ∀ (K : Type) [Field K], Group (originGroup K)
  infinityGroupStructure : ∀ (K : Type) [Field K], Group (infinityGroup K)
  wildOrigin : ∀ (K : Type) [Field K], Subgroup (originGroup K)
  origin : ∀ (K : Type) [Field K],
    C (ArithmeticSourceMaps.fiberScheme K) ⥤ FDRep (PadicAlgCl 2) (originGroup K)
  infinity : ∀ (K : Type) [Field K],
    C (ArithmeticSourceMaps.fiberScheme K) ⥤ FDRep (PadicAlgCl 2) (infinityGroup K)
  profile : ∀ (K : Type) [Field K], C (ArithmeticSourceMaps.fiberScheme K) → BreakProfile
  profile_dimension : ∀ (K : Type) [Field K] (A : C (ArithmeticSourceMaps.fiberScheme K)),
    (profile K A).rank = Module.finrank (PadicAlgCl 2) ((infinity K).obj A)
  profile_localIso : ∀ (K : Type) [Field K]
    (A B : C (ArithmeticSourceMaps.fiberScheme K)),
    ((infinity K).obj A ≅ (infinity K).obj B) →
      (profile K A).multiplicity = (profile K B).multiplicity

attribute [instance] LocalRealization.originGroupStructure LocalRealization.infinityGroupStructure

variable (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (M : LocalRealization C)

def tameZero (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K)) : Prop :=
  wildTrivial (M.wildOrigin K) ((M.origin K).obj
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A))

def breaksLE (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K)) (s : ℚ) : Prop :=
  ∀ r ∈ (M.profile K ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)).multiplicity.support,
    r ≤ s

def isoclinic (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K)) (s : ℚ) : Prop :=
  ∀ r ∈ (M.profile K ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)).multiplicity.support,
    r = s

/-- Bind the three local observables by construction, preserving the chosen
rank and whole-Gm lissity fields. Rank is not identified with a local dimension. -/
def observables (K : Type) [Field K]
    (lisseOnUnits : C (StartingSourceMaps.affineLine K) → Prop)
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine K)) where
  LisseOnUnits := lisseOnUnits
  rank := rank
  TameZero := tameZero C U M K
  BreaksLE := breaksLE C U M K
  Isoclinic := isoclinic C U M K

theorem observables_lisseOnUnits (K : Type) [Field K]
    (lisseOnUnits : C (StartingSourceMaps.affineLine K) → Prop)
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U M K lisseOnUnits rank).LisseOnUnits = lisseOnUnits := rfl

theorem observables_rank (K : Type) [Field K]
    (lisseOnUnits : C (StartingSourceMaps.affineLine K) → Prop)
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U M K lisseOnUnits rank).rank = rank := rfl

theorem observables_tameZero (K : Type) [Field K]
    (lisseOnUnits : C (StartingSourceMaps.affineLine K) → Prop)
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U M K lisseOnUnits rank).TameZero = tameZero C U M K := rfl

theorem observables_breaksLE (K : Type) [Field K]
    (lisseOnUnits : C (StartingSourceMaps.affineLine K) → Prop)
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U M K lisseOnUnits rank).BreaksLE = breaksLE C U M K := rfl

theorem observables_isoclinic (K : Type) [Field K]
    (lisseOnUnits : C (StartingSourceMaps.affineLine K) → Prop)
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U M K lisseOnUnits rank).Isoclinic = isoclinic C U M K := rfl

theorem tameZero_iso (K : Type) [Field K]
    {A B : C (StartingSourceMaps.affineLine K)} (e : A ≅ B)
    (h : tameZero C U M K A) : tameZero C U M K B :=
  wildTrivial_iso _ ((M.origin K).mapIso ((U.pull
    (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e)) h

theorem breaksLE_iso (K : Type) [Field K]
    {A B : C (StartingSourceMaps.affineLine K)} (e : A ≅ B)
    (s : ℚ) (h : breaksLE C U M K A s) : breaksLE C U M K B s := by
  intro r hr
  apply h r
  rwa [← M.profile_localIso K _ _ ((M.infinity K).mapIso
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e))] at hr

theorem isoclinic_iso (K : Type) [Field K]
    {A B : C (StartingSourceMaps.affineLine K)} (e : A ≅ B)
    (s : ℚ) (h : isoclinic C U M K A s) : isoclinic C U M K B s := by
  intro r hr
  apply h r
  rwa [← M.profile_localIso K _ _ ((M.infinity K).mapIso
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e))] at hr

variable (O : Constructions C)
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅
      𝟭 (C (ArithmeticSourceMaps.fiberScheme K)))
  (originTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (z : ℤ),
    O.tate K h2 z ⋙ M.origin K ≅ M.origin K)
  (infinityTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (z : ℤ),
    O.tate K h2 z ⋙ M.infinity K ≅ M.infinity K)
  (rawKatzOrigin : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    wildTrivial (M.wildOrigin K)
      ((M.origin K).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))))
  (rawKatzInfinity : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    Module.finrank (PadicAlgCl 2)
      ((M.infinity K).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))) = n ∧
    (M.profile K (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).multiplicity 0 = 0 ∧
    (M.profile K (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).swan = 1)

omit [∀ X, Abelian (C X)] in
include originTate rawKatzOrigin in
/-- Every raw rank and every integer Tate twist has tame origin. -/
theorem kloosterman_tate_tame (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (n : ℕ) (hn : 0 < n) (z : ℤ) :
    wildTrivial (M.wildOrigin K) ((M.origin K).obj
      ((O.tate K h2 z).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0)))) :=
  wildTrivial_iso _ ((originTate K h2 z).app _).symm
    (rawKatzOrigin K h2 ψ hψ n hn)

omit [∀ X, Abelian (C X)] in
include infinityTate rawKatzInfinity in
/-- Every raw rank and every integer Tate twist has the computed break support. -/
theorem kloosterman_tate_support (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (n : ℕ) (hn : 0 < n) (z : ℤ) :
    (M.profile K ((O.tate K h2 z).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0)))).multiplicity.support =
      {1 / (n : ℚ)} := by
  let raw := O.katz K h2 (kloostermanIndex ψ hψ n hn 0)
  have he := M.profile_localIso K ((O.tate K h2 z).obj raw) raw
    ((infinityTate K h2 z).app raw)
  rw [he]
  obtain ⟨hd, ht, hs⟩ := rawKatzInfinity K h2 ψ hψ n hn
  exact BreakProfile.support_of_totallyWild_swan_one _ n hn
    ((M.profile_dimension K _).trans hd) ht hs

include zeroRestriction originTate rawKatzOrigin in
/-- The normalized rank-three original recipe has computed tame origin. -/
theorem normalized_kloosterman_tame (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    tameZero C U M K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) := by
  apply wildTrivial_iso _ ((M.origin K).mapIso
    (normalizedKlRestrictionIso K C U O zeroRestriction h2 ψ hψ)).symm
  exact kloosterman_tate_tame C M O originTate rawKatzOrigin K h2 ψ hψ 3 (by decide) 1

include zeroRestriction infinityTate rawKatzInfinity in
theorem normalized_kloosterman_isoclinic (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    isoclinic C U M K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) (1 / 3) := by
  intro r hr
  have he := M.profile_localIso K _ _ ((M.infinity K).mapIso
    (normalizedKlRestrictionIso K C U O zeroRestriction h2 ψ hψ))
  rw [he] at hr
  have hs := kloosterman_tate_support C M O infinityTate rawKatzInfinity
    K h2 ψ hψ 3 (by decide) 1
  change r ∈ (M.profile K ((O.tate K h2 1).obj
    (O.katz K h2 (kloostermanIndex ψ hψ 3 (by decide) 0)))).multiplicity.support at hr
  rw [hs] at hr
  exact Finset.mem_singleton.mp hr

include zeroRestriction infinityTate rawKatzInfinity in
theorem normalized_kloosterman_breaks (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    breaksLE C U M K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) (1 / 3) := by
  intro r hr
  exact le_of_eq (normalized_kloosterman_isoclinic C U M O zeroRestriction infinityTate
    rawKatzInfinity K h2 ψ hψ r hr)

variable (L : ∀ X : Scheme, ObjectProperty (C X))
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
    L (StartingSourceMaps.affineLine K) (O.artinSchreier K h2 ψ))
  (smoothOriginUnramified : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)),
    L (StartingSourceMaps.affineLine K) A →
    wildTrivial (M.wildOrigin K) ((M.origin K).obj
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)))
  (standardASInfinity : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
    Module.finrank (PadicAlgCl 2) ((M.infinity K).obj
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj
        (O.artinSchreier K h2 ψ))) = 1 ∧
    (M.profile K ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj
      (O.artinSchreier K h2 ψ))).swan = 1)

include standardASLisse smoothOriginUnramified in
theorem artinSchreier_tame (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    tameZero C U M K (O.artinSchreier K h2 ψ) :=
  smoothOriginUnramified K h2 _ (standardASLisse K h2 ψ hψ)

include standardASInfinity in
theorem artinSchreier_isoclinic (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    isoclinic C U M K (O.artinSchreier K h2 ψ) 1 := by
  intro r hr
  obtain ⟨hd, hs⟩ := standardASInfinity K h2 ψ hψ
  have he := BreakProfile.support_of_rank_one_swan_one _
    ((M.profile_dimension K _).trans hd) hs
  rw [he] at hr
  exact Finset.mem_singleton.mp hr

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1)

include zeroRestriction originTate rawKatzOrigin hψ in
theorem primitive_kl_tame : tameZero C U M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) := by
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial
    C O p h2 ψ hψ]
  exact normalized_kloosterman_tame C U M O zeroRestriction originTate rawKatzOrigin
    (ZMod p) h2 ψ hψ

include zeroRestriction infinityTate rawKatzInfinity hψ in
theorem primitive_kl_breaks : breaksLE C U M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) (1 / 3) := by
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial
    C O p h2 ψ hψ]
  exact normalized_kloosterman_breaks C U M O zeroRestriction infinityTate rawKatzInfinity
    (ZMod p) h2 ψ hψ

include standardASLisse smoothOriginUnramified hψ in
theorem primitive_as_tame : tameZero C U M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) :=
  artinSchreier_tame C U M O L standardASLisse smoothOriginUnramified (ZMod p) h2 ψ hψ

include standardASInfinity hψ in
theorem primitive_as_isoclinic : isoclinic C U M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) 1 :=
  artinSchreier_isoclinic C U M O standardASInfinity (ZMod p) h2 ψ hψ

end PrimeGap182.TypeIII.PrimitiveRamificationFromGeneralKatzTheory
