import TypeIIIPrimitiveRamificationFromGeneralKatzTheory
import TypeIIISourceGlobalLissityFromKatzPullbacks
import TypeIIIPrimitiveRanksFromComputedGenericLineRank

/-!
# Globally lisse line local predicates from the same Katz constructions

Each local predicate is actual whole-Gm lissity of SAME-U restriction
conjoined with the existing actual wild-inertia or finite-break predicate.
The rank function is preserved; no rank or Swan equality is included in a
predicate. The original four guarded Kl3/AS primitive local clauses follow
from the existing general lissity, Katz local and geometric Tate laws.
Actual adic/inertia/upper-break interpretation remains external model data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory

namespace PrimeGap182.TypeIII.GloballyLisseLineRamificationFromKatz
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : PrimitiveRamificationFromGeneralKatzTheory.LocalRealization C)

def tameZero (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K)) : Prop :=
  SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A ∧
    PrimitiveRamificationFromGeneralKatzTheory.tameZero C U M K A

def breaksLE (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K)) (s : ℚ) : Prop :=
  SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A ∧
    PrimitiveRamificationFromGeneralKatzTheory.breaksLE C U M K A s

def isoclinic (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K)) (s : ℚ) : Prop :=
  SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A ∧
    PrimitiveRamificationFromGeneralKatzTheory.isoclinic C U M K A s

/-- Preserve the supplied rank, allowing the caller's computed generic rank
without a rank realization or equality hypothesis. -/
def observables (K : Type) [Field K]
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine K)) where
  LisseOnUnits := SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L
  rank := rank
  TameZero := tameZero C U L M K
  BreaksLE := breaksLE C U L M K
  Isoclinic := isoclinic C U L M K

theorem observables_lisseOnUnits (K : Type) [Field K]
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U L M K rank).LisseOnUnits =
      SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L := rfl

theorem observables_rank (K : Type) [Field K]
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U L M K rank).rank = rank := rfl

theorem observables_tameZero (K : Type) [Field K]
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U L M K rank).TameZero = tameZero C U L M K := rfl

theorem observables_breaksLE (K : Type) [Field K]
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U L M K rank).BreaksLE = breaksLE C U L M K := rfl

theorem observables_isoclinic (K : Type) [Field K]
    (rank : C (StartingSourceMaps.affineLine K) → ℕ) :
    (observables C U L M K rank).Isoclinic = isoclinic C U L M K := rfl

/-- The existing SAME-U actual generic line rank is used directly. -/
def canonicalObservables
    (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
    (K : Type) [Field K] :
    LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine K)) :=
  observables C U L M K (PrimitiveRanksFromComputedGenericLineRank.canonicalLineRank C U G K)

theorem canonicalObservables_rank
    (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
    (K : Type) [Field K] :
    (canonicalObservables C U L M G K).rank =
      PrimitiveRanksFromComputedGenericLineRank.canonicalLineRank C U G K := rfl

theorem tameZero_lisse (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K))
    (h : tameZero C U L M K A) :
    SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A := h.1

theorem breaksLE_lisse (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K))
    (s : ℚ) (h : breaksLE C U L M K A s) :
    SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A := h.1

theorem isoclinic_lisse (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K))
    (s : ℚ) (h : isoclinic C U L M K A s) :
    SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A := h.1

theorem tameZero_local (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K))
    (h : tameZero C U L M K A) :
    PrimitiveRamificationFromGeneralKatzTheory.tameZero C U M K A := h.2

theorem breaksLE_local (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K))
    (s : ℚ) (h : breaksLE C U L M K A s) :
    PrimitiveRamificationFromGeneralKatzTheory.breaksLE C U M K A s := h.2

theorem isoclinic_local (K : Type) [Field K] (A : C (StartingSourceMaps.affineLine K))
    (s : ℚ) (h : isoclinic C U L M K A s) :
    PrimitiveRamificationFromGeneralKatzTheory.isoclinic C U M K A s := h.2

section Isomorphisms
variable [∀ X, (L X).IsClosedUnderIsomorphisms]

theorem tameZero_iso (K : Type) [Field K] {A B : C (StartingSourceMaps.affineLine K)}
    (e : A ≅ B) (h : tameZero C U L M K A) : tameZero C U L M K B :=
  ⟨(L _).prop_of_iso ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e) h.1,
    PrimitiveRamificationFromGeneralKatzTheory.tameZero_iso C U M K e h.2⟩

theorem breaksLE_iso (K : Type) [Field K] {A B : C (StartingSourceMaps.affineLine K)}
    (e : A ≅ B) (s : ℚ) (h : breaksLE C U L M K A s) : breaksLE C U L M K B s :=
  ⟨(L _).prop_of_iso ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e) h.1,
    PrimitiveRamificationFromGeneralKatzTheory.breaksLE_iso C U M K e s h.2⟩

theorem isoclinic_iso (K : Type) [Field K] {A B : C (StartingSourceMaps.affineLine K)}
    (e : A ≅ B) (s : ℚ) (h : isoclinic C U L M K A s) : isoclinic C U L M K B s :=
  ⟨(L _).prop_of_iso ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso e) h.1,
    PrimitiveRamificationFromGeneralKatzTheory.isoclinic_iso C U M K e s h.2⟩
end Isomorphisms

variable (O : Constructions C)
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅
      𝟭 (C (ArithmeticSourceMaps.fiberScheme K)))
  (unequalKatzLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), a.upper.length ≠ a.lower.length →
      L (ArithmeticSourceMaps.fiberScheme K) (member C O K h2 a))
  (originTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (z : ℤ),
    O.tate K h2 z ⋙ M.origin K ≅ M.origin K)
  (infinityTate : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (z : ℤ),
    O.tate K h2 z ⋙ M.infinity K ≅ M.infinity K)
  (rawKatzOrigin : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    PrimitiveRamificationFromGeneralKatzTheory.wildTrivial (M.wildOrigin K)
      ((M.origin K).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))))
  (rawKatzInfinity : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n),
    Module.finrank (PadicAlgCl 2)
      ((M.infinity K).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))) = n ∧
    (M.profile K (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).multiplicity 0 = 0 ∧
    (M.profile K (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))).swan = 1)

section Kloosterman
variable [∀ X, (L X).IsClosedUnderIsomorphisms]

include zeroRestriction unequalKatzLisse originTate rawKatzOrigin in
theorem normalized_kloosterman_tame (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    tameZero C U L M K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) :=
  ⟨SourceGlobalLissityFromKatzPullbacks.normalizedKl_restriction_lisse K C U L O
      zeroRestriction unequalKatzLisse h2 ψ hψ,
    PrimitiveRamificationFromGeneralKatzTheory.normalized_kloosterman_tame C U M O
      zeroRestriction originTate rawKatzOrigin K h2 ψ hψ⟩

include zeroRestriction unequalKatzLisse infinityTate rawKatzInfinity in
theorem normalized_kloosterman_breaks (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    breaksLE C U L M K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) (1 / 3) :=
  ⟨SourceGlobalLissityFromKatzPullbacks.normalizedKl_restriction_lisse K C U L O
      zeroRestriction unequalKatzLisse h2 ψ hψ,
    PrimitiveRamificationFromGeneralKatzTheory.normalized_kloosterman_breaks C U M O
      zeroRestriction infinityTate rawKatzInfinity K h2 ψ hψ⟩

include zeroRestriction unequalKatzLisse infinityTate rawKatzInfinity in
theorem normalized_kloosterman_isoclinic (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    isoclinic C U L M K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) (1 / 3) :=
  ⟨SourceGlobalLissityFromKatzPullbacks.normalizedKl_restriction_lisse K C U L O
      zeroRestriction unequalKatzLisse h2 ψ hψ,
    PrimitiveRamificationFromGeneralKatzTheory.normalized_kloosterman_isoclinic C U M O
      zeroRestriction infinityTate rawKatzInfinity K h2 ψ hψ⟩

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1)

include zeroRestriction unequalKatzLisse originTate rawKatzOrigin hψ in
theorem primitive_kl_tame : tameZero C U L M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) := by
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial
    C O p h2 ψ hψ]
  exact normalized_kloosterman_tame C U L M O zeroRestriction unequalKatzLisse originTate
    rawKatzOrigin (ZMod p) h2 ψ hψ

include zeroRestriction unequalKatzLisse infinityTate rawKatzInfinity hψ in
theorem primitive_kl_breaks : breaksLE C U L M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) (1 / 3) := by
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial
    C O p h2 ψ hψ]
  exact normalized_kloosterman_breaks C U L M O zeroRestriction unequalKatzLisse infinityTate
    rawKatzInfinity (ZMod p) h2 ψ hψ
end Kloosterman

variable
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
    L (StartingSourceMaps.affineLine K) (O.artinSchreier K h2 ψ))
  (smoothOriginUnramified : ∀ (K : Type) [Field K] (_h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)), L (StartingSourceMaps.affineLine K) A →
    PrimitiveRamificationFromGeneralKatzTheory.wildTrivial (M.wildOrigin K) ((M.origin K).obj
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)))
  (standardASInfinity : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K (PadicAlgCl 2)), ψ ≠ 1 →
    Module.finrank (PadicAlgCl 2) ((M.infinity K).obj
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj (O.artinSchreier K h2 ψ))) = 1 ∧
    (M.profile K ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj
      (O.artinSchreier K h2 ψ))).swan = 1)

include lissePull standardASLisse smoothOriginUnramified in
theorem artinSchreier_tame (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    tameZero C U L M K (O.artinSchreier K h2 ψ) :=
  ⟨lissePull _ _ (standardASLisse K h2 ψ hψ),
    PrimitiveRamificationFromGeneralKatzTheory.artinSchreier_tame C U M O L standardASLisse
      smoothOriginUnramified K h2 ψ hψ⟩

include lissePull standardASLisse standardASInfinity in
theorem artinSchreier_isoclinic (K : Type) [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    isoclinic C U L M K (O.artinSchreier K h2 ψ) 1 :=
  ⟨lissePull _ _ (standardASLisse K h2 ψ hψ),
    PrimitiveRamificationFromGeneralKatzTheory.artinSchreier_isoclinic C U M O standardASInfinity
      K h2 ψ hψ⟩

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
  (ψ : AddChar (ZMod p) (PadicAlgCl 2)) (hψ : ψ ≠ 1)

include lissePull standardASLisse smoothOriginUnramified hψ in
theorem primitive_as_tame : tameZero C U L M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) :=
  artinSchreier_tame C U L M O lissePull standardASLisse smoothOriginUnramified (ZMod p) h2 ψ hψ

include lissePull standardASLisse standardASInfinity hψ in
theorem primitive_as_isoclinic : isoclinic C U L M (ZMod p)
    ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) 1 :=
  artinSchreier_isoclinic C U L M O lissePull standardASLisse standardASInfinity (ZMod p) h2 ψ hψ

end PrimeGap182.TypeIII.GloballyLisseLineRamificationFromKatz
