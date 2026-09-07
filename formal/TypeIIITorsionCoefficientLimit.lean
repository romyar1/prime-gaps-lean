import TypeIIITorsionCoefficients
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Category.Profinite.Basic

/-!
# The actual inverse-limit coefficient ring

The coefficient ring is the subring of sequences in the proved finite
cyclotomic quotients whose coordinates agree under every reduction map.
The coordinate projections and the unique lift of a compatible family
of ring homomorphisms give its inverse-limit universal property.

The distinguished root and additive character reduce to their actual
finite-level counterparts.  When p and ℓ are distinct primes, the root
is primitive, as detected at level zero, and the compatible inverses of
p give an actual unit in the limit ring.

Each level is explicitly given the discrete topology, only locally in
the topology proofs below.  The limit has the product subspace topology.
Its defining compatibility equations form a closed subset, proving
compactness, Hausdorffness, and total disconnectedness.  Ring operations
and the coordinate projections are continuous.

No local factor, coefficient field, adic-field identification, sheaf
comparison, cohomology, or weight theorem is asserted.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped Classical

/-- The actual subring of compatible sequences in the coefficient tower. -/
def torsionCoefficientLimitSubring (p ell : ℕ) :
    Subring (∀ n : ℕ, TorsionCoefficientRing p ell n) where
  carrier := {x | ∀ (m n : ℕ) (hmn : m ≤ n), torsionCoefficientReduce p ell hmn (x n) = x m}
  zero_mem' := by
    intro m n hmn
    exact map_zero (torsionCoefficientReduce p ell hmn)
  one_mem' := by
    intro m n hmn
    exact map_one (torsionCoefficientReduce p ell hmn)
  add_mem' hx hy := by
    intro m n hmn
    change torsionCoefficientReduce p ell hmn (_ + _) = _ + _
    rw [map_add, hx m n hmn, hy m n hmn]
  neg_mem' hx := by
    intro m n hmn
    change torsionCoefficientReduce p ell hmn (-_) = -_
    rw [map_neg, hx m n hmn]
  mul_mem' hx hy := by
    intro m n hmn
    change torsionCoefficientReduce p ell hmn (_ * _) = _ * _
    rw [map_mul, hx m n hmn, hy m n hmn]

/-- The inverse-limit ring, with coordinatewise ring operations. -/
abbrev TorsionCoefficientLimit (p ell : ℕ) := ↥(torsionCoefficientLimitSubring p ell)

/-- The literal ring homomorphism projecting a compatible sequence to a level. -/
def torsionCoefficientLimitProjection (p ell n : ℕ) :
    TorsionCoefficientLimit p ell →+* TorsionCoefficientRing p ell n :=
  (Pi.evalRingHom (TorsionCoefficientRing p ell) n).comp
    (torsionCoefficientLimitSubring p ell).subtype

@[simp] theorem torsionCoefficientLimitProjection_apply (p ell n : ℕ)
    (x : TorsionCoefficientLimit p ell) :
    torsionCoefficientLimitProjection p ell n x = x.val n := rfl

/-- Equality of all finite coordinates is equality in the actual ring. -/
@[ext] theorem torsionCoefficientLimit_ext (p ell : ℕ)
    {x y : TorsionCoefficientLimit p ell}
    (h : ∀ n, torsionCoefficientLimitProjection p ell n x =
      torsionCoefficientLimitProjection p ell n y) : x = y :=
  Subtype.ext (funext h)

/-- The actual projection homomorphisms commute with reduction. -/
theorem torsionCoefficientLimitProjection_compatible (p ell : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    (torsionCoefficientReduce p ell hmn).comp (torsionCoefficientLimitProjection p ell n) =
      torsionCoefficientLimitProjection p ell m := by
  ext x
  exact x.property m n hmn

/-- A compatible family of ring homomorphisms has an actual coordinatewise lift. -/
def torsionCoefficientLimitLift (p ell : ℕ) {A : Type*} [CommRing A]
    (f : ∀ n, A →+* TorsionCoefficientRing p ell n)
    (hf : ∀ (m n : ℕ) (hmn : m ≤ n), (torsionCoefficientReduce p ell hmn).comp (f n) = f m) :
    A →+* TorsionCoefficientLimit p ell where
  toFun a := ⟨fun n => f n a, fun m n hmn => RingHom.congr_fun (hf m n hmn) a⟩
  map_zero' := by apply torsionCoefficientLimit_ext; intro n; exact map_zero (f n)
  map_one' := by apply torsionCoefficientLimit_ext; intro n; exact map_one (f n)
  map_add' a b := by apply torsionCoefficientLimit_ext; intro n; exact map_add (f n) a b
  map_mul' a b := by apply torsionCoefficientLimit_ext; intro n; exact map_mul (f n) a b

@[simp] theorem torsionCoefficientLimitProjection_lift (p ell : ℕ) {A : Type*} [CommRing A]
    (f : ∀ n, A →+* TorsionCoefficientRing p ell n)
    (hf : ∀ (m n : ℕ) (hmn : m ≤ n), (torsionCoefficientReduce p ell hmn).comp (f n) = f m)
    (n : ℕ) :
    (torsionCoefficientLimitProjection p ell n).comp (torsionCoefficientLimitLift p ell f hf) =
      f n := by
  ext a
  rfl

/-- Maps into the limit are determined by their actual coordinate homomorphisms. -/
theorem torsionCoefficientLimit_hom_ext (p ell : ℕ) {A : Type*} [CommRing A]
    {f g : A →+* TorsionCoefficientLimit p ell}
    (h : ∀ n, (torsionCoefficientLimitProjection p ell n).comp f =
      (torsionCoefficientLimitProjection p ell n).comp g) : f = g := by
  apply RingHom.ext
  intro a
  apply torsionCoefficientLimit_ext
  intro n
  exact RingHom.congr_fun (h n) a

/-- The coordinatewise lift is the unique ring homomorphism with those projections. -/
theorem torsionCoefficientLimitLift_unique (p ell : ℕ) {A : Type*} [CommRing A]
    (f : ∀ n, A →+* TorsionCoefficientRing p ell n)
    (hf : ∀ (m n : ℕ) (hmn : m ≤ n), (torsionCoefficientReduce p ell hmn).comp (f n) = f m)
    (g : A →+* TorsionCoefficientLimit p ell)
    (hg : ∀ n, (torsionCoefficientLimitProjection p ell n).comp g = f n) :
    g = torsionCoefficientLimitLift p ell f hf := by
  apply torsionCoefficientLimit_hom_ext
  intro n
  rw [torsionCoefficientLimitProjection_lift, hg n]

/-- Nontriviality is detected by the actual projection to the nontrivial level zero. -/
instance torsionCoefficientLimit_nontrivial (p ell : ℕ)
    [Fact p.Prime] [Fact ell.Prime] : Nontrivial (TorsionCoefficientLimit p ell) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h₀ : (0 : TorsionCoefficientRing p ell 0) = 1 := by
    simpa only [map_zero, map_one] using congrArg (torsionCoefficientLimitProjection p ell 0) h
  exact zero_ne_one h₀

/-- The actual compatible sequence of distinguished cyclotomic roots. -/
def torsionCoefficientLimitRoot (p ell : ℕ) : TorsionCoefficientLimit p ell :=
  ⟨fun n => torsionCoefficientRoot p ell n,
    fun _ _ hmn => torsionCoefficientReduce_root p ell hmn⟩

@[simp] theorem torsionCoefficientLimitProjection_root (p ell n : ℕ) :
    torsionCoefficientLimitProjection p ell n (torsionCoefficientLimitRoot p ell) =
      torsionCoefficientRoot p ell n := rfl

theorem torsionCoefficientLimitRoot_pow (p ell : ℕ) :
    torsionCoefficientLimitRoot p ell ^ p = 1 := by
  apply torsionCoefficientLimit_ext
  intro n
  simpa only [map_pow, map_one, torsionCoefficientLimitProjection_root] using
    torsionCoefficientRoot_pow p ell n

/-- An actual compatible sequence of inverses of p; compatibility uses
uniqueness of an inverse after applying the reduction homomorphism. -/
def torsionCoefficientLimitPInverse (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) : TorsionCoefficientLimit p ell := by
  let (n : ℕ) : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  refine ⟨fun n => ⅟(p : TorsionCoefficientRing p ell n), ?_⟩
  intro m n hmn
  apply (invOf_eq_left_inv ?_).symm
  rw [← map_natCast (torsionCoefficientReduce p ell hmn) p,
    ← map_mul, invOf_mul_self, map_one]

theorem torsionCoefficientLimitPInverse_mul (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) :
    torsionCoefficientLimitPInverse p ell hne * (p : TorsionCoefficientLimit p ell) = 1 := by
  apply torsionCoefficientLimit_ext
  intro n
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  change ⅟(p : TorsionCoefficientRing p ell n) * (p : TorsionCoefficientRing p ell n) = 1
  exact invOf_mul_self _

/-- The inverse and its two multiplication identities give actual invertibility of p. -/
@[instance_reducible]
def torsionCoefficientLimitPInvertible (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) : Invertible (p : TorsionCoefficientLimit p ell) where
  invOf := torsionCoefficientLimitPInverse p ell hne
  invOf_mul_self := torsionCoefficientLimitPInverse_mul p ell hne
  mul_invOf_self := by rw [mul_comm, torsionCoefficientLimitPInverse_mul]

theorem torsionCoefficientLimit_p_isUnit (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) : IsUnit (p : TorsionCoefficientLimit p ell) := by
  let := torsionCoefficientLimitPInvertible p ell hne
  exact isUnit_of_invertible _

/-- The root is nontrivial because its level-zero projection is nontrivial. -/
theorem torsionCoefficientLimitRoot_ne_one (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) : torsionCoefficientLimitRoot p ell ≠ 1 := by
  intro h
  apply torsionCoefficientRoot_ne_one p ell 0 hne
  simpa only [torsionCoefficientLimitProjection_root, map_one] using
    congrArg (torsionCoefficientLimitProjection p ell 0) h

/-- The actual limit root has exact order p. -/
theorem torsionCoefficientLimitRoot_isPrimitive (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) : IsPrimitiveRoot (torsionCoefficientLimitRoot p ell) p := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one (torsionCoefficientLimitRoot_pow p ell)) with h | h
  · exact False.elim (torsionCoefficientLimitRoot_ne_one p ell hne (orderOf_eq_one_iff.mp h))
  · exact h

/-- The additive character into the actual limit ring. -/
def torsionCoefficientLimitChar (p ell : ℕ) [Fact p.Prime] :
    AddChar (ZMod p) (TorsionCoefficientLimit p ell) :=
  AddChar.zmodChar p (torsionCoefficientLimitRoot_pow p ell)

@[simp] theorem torsionCoefficientLimitChar_apply (p ell : ℕ) [Fact p.Prime] (a : ZMod p) :
    torsionCoefficientLimitChar p ell a = torsionCoefficientLimitRoot p ell ^ a.val := rfl

/-- Its actual coordinates are exactly the previously constructed finite characters. -/
@[simp] theorem torsionCoefficientLimitProjection_char (p ell n : ℕ) [Fact p.Prime]
    (a : ZMod p) :
    torsionCoefficientLimitProjection p ell n (torsionCoefficientLimitChar p ell a) =
      torsionCoefficientChar p ell n a := by
  simp only [torsionCoefficientLimitChar_apply, map_pow, torsionCoefficientLimitProjection_root,
    torsionCoefficientChar_apply]

theorem torsionCoefficientLimitProjection_comp_char (p ell n : ℕ) [Fact p.Prime] :
    (torsionCoefficientLimitProjection p ell n).toMonoidHom.compAddChar
        (torsionCoefficientLimitChar p ell) = torsionCoefficientChar p ell n := by
  ext a
  exact torsionCoefficientLimitProjection_char p ell n a

theorem torsionCoefficientLimitChar_isPrimitive (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) : (torsionCoefficientLimitChar p ell).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root p
    (torsionCoefficientLimitRoot_isPrimitive p ell hne)

section Topology

/-- The explicitly chosen discrete topology of a finite coefficient level.
It is a named definition, not an exported global instance on existing rings. -/
@[instance_reducible]
def torsionCoefficientLevelTopology (p ell n : ℕ) :
    TopologicalSpace (TorsionCoefficientRing p ell n) := ⊥

attribute [local instance] torsionCoefficientLevelTopology

/-- The chosen finite-level topology is discrete by its definition. -/
theorem torsionCoefficientLevel_discreteTopology (p ell n : ℕ) :
    DiscreteTopology (TorsionCoefficientRing p ell n) := ⟨rfl⟩

attribute [local instance] torsionCoefficientLevel_discreteTopology

/-- The limit has the subspace topology of the product of the named discrete levels. -/
instance torsionCoefficientLimit_topologicalSpace (p ell : ℕ) :
    TopologicalSpace (TorsionCoefficientLimit p ell) :=
  TopologicalSpace.induced (fun x : TorsionCoefficientLimit p ell => x.val)
    (inferInstance : TopologicalSpace (∀ n : ℕ, TorsionCoefficientRing p ell n))

/-- Every compatibility equation is a closed equalizer of continuous maps. -/
theorem torsionCoefficientLimitSubring_isClosed (p ell : ℕ) :
    IsClosed (torsionCoefficientLimitSubring p ell : Set (∀ n : ℕ, TorsionCoefficientRing p ell n)) := by
  change IsClosed {x : ∀ n : ℕ, TorsionCoefficientRing p ell n | ∀ (m n : ℕ) (hmn : m ≤ n),
    torsionCoefficientReduce p ell hmn (x n) = x m}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun hmn => ?_
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (torsionCoefficientReduce p ell hmn)).comp
      (continuous_apply n)) (continuous_apply m)

/-- Tychonoff compactness of the finite levels and the proved closedness
give actual compactness of the inverse-limit ring. -/
instance torsionCoefficientLimit_compactSpace (p ell : ℕ) [Fact ell.Prime] :
    CompactSpace (TorsionCoefficientLimit p ell) :=
  isCompact_iff_compactSpace.mp (torsionCoefficientLimitSubring_isClosed p ell).isCompact

instance torsionCoefficientLimit_t2Space (p ell : ℕ) :
    T2Space (TorsionCoefficientLimit p ell) := inferInstance

instance torsionCoefficientLimit_totallyDisconnectedSpace (p ell : ℕ) :
    TotallyDisconnectedSpace (TorsionCoefficientLimit p ell) := inferInstance

/-- Addition, negation, and multiplication are continuous in the actual limit topology. -/
instance torsionCoefficientLimit_isTopologicalRing (p ell : ℕ) :
    IsTopologicalRing (TorsionCoefficientLimit p ell) := inferInstance

/-- Projection is continuous for the explicitly named discrete topology at its level. -/
theorem torsionCoefficientLimitProjection_continuous (p ell n : ℕ) :
    Continuous (torsionCoefficientLimitProjection p ell n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- A compatible family of continuous ring homomorphisms has a continuous
lift into the actual product-subspace topology. -/
theorem torsionCoefficientLimitLift_continuous (p ell : ℕ)
    {A : Type*} [CommRing A] [TopologicalSpace A]
    (f : ∀ n, A →+* TorsionCoefficientRing p ell n)
    (hf : ∀ (m n : ℕ) (hmn : m ≤ n), (torsionCoefficientReduce p ell hmn).comp (f n) = f m)
    (hc : ∀ n, Continuous (f n)) :
    Continuous (torsionCoefficientLimitLift p ell f hf) :=
  (continuous_pi hc).subtype_mk _

/-- The proved compact Hausdorff totally disconnected space underlying the limit ring. -/
def torsionCoefficientLimitProfinite (p ell : ℕ) [Fact ell.Prime] : Profinite :=
  Profinite.of (TorsionCoefficientLimit p ell)

end Topology

#print axioms torsionCoefficientLimitSubring
#print axioms TorsionCoefficientLimit
#print axioms torsionCoefficientLimitProjection
#print axioms torsionCoefficientLimitProjection_apply
#print axioms torsionCoefficientLimit_ext
#print axioms torsionCoefficientLimitProjection_compatible
#print axioms torsionCoefficientLimitLift
#print axioms torsionCoefficientLimitProjection_lift
#print axioms torsionCoefficientLimit_hom_ext
#print axioms torsionCoefficientLimitLift_unique
#print axioms torsionCoefficientLimit_nontrivial
#print axioms torsionCoefficientLimitRoot
#print axioms torsionCoefficientLimitProjection_root
#print axioms torsionCoefficientLimitRoot_pow
#print axioms torsionCoefficientLimitPInverse
#print axioms torsionCoefficientLimitPInverse_mul
#print axioms torsionCoefficientLimitPInvertible
#print axioms torsionCoefficientLimit_p_isUnit
#print axioms torsionCoefficientLimitRoot_ne_one
#print axioms torsionCoefficientLimitRoot_isPrimitive
#print axioms torsionCoefficientLimitChar
#print axioms torsionCoefficientLimitChar_apply
#print axioms torsionCoefficientLimitProjection_char
#print axioms torsionCoefficientLimitProjection_comp_char
#print axioms torsionCoefficientLimitChar_isPrimitive
#print axioms torsionCoefficientLevelTopology
#print axioms torsionCoefficientLevel_discreteTopology
#print axioms torsionCoefficientLimit_topologicalSpace
#print axioms torsionCoefficientLimitSubring_isClosed
#print axioms torsionCoefficientLimit_compactSpace
#print axioms torsionCoefficientLimit_t2Space
#print axioms torsionCoefficientLimit_totallyDisconnectedSpace
#print axioms torsionCoefficientLimit_isTopologicalRing
#print axioms torsionCoefficientLimitProjection_continuous
#print axioms torsionCoefficientLimitLift_continuous
#print axioms torsionCoefficientLimitProfinite

end PrimeGap182.TypeIII
