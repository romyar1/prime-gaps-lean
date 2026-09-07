import TypeIIIHenselianEtaleLifting
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# Unique lifting of coprime monic factorizations

For a henselian local ring R, coefficient reduction gives a bijection
between coprime monic factorizations of a fixed monic polynomial over R
and such factorizations of its residue polynomial, with specified ordered
factor degrees.  The construction uses Mathlib's actual universal coprime
factorization algebra, its proved étaleness, and the actual bijection on
residue-field points proved in TypeIIIHenselianEtaleLifting.

The coefficient-map formulas identify the resulting equivalence and its
inverse with the original polynomial reductions.  Uniqueness already
holds over an arbitrary local ring.  No factorization-lifting property,
finite-algebra henselianity, or proper clopen-lifting theorem is assumed.
-/

noncomputable section

universe u v w z

namespace PrimeGap182.TypeIII.HenselianFactorizationLifting

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R]

/-- Actual ordered coprime monic factorizations of the coefficient image of p. -/
abbrev CoprimeFactorization (S : Type v) [CommRing S] [Algebra R S]
    (m k : ℕ) (p : MonicDegreeEq R (m + k)) :=
  {q : MonicDegreeEq S m × MonicDegreeEq S k //
    q.1.1 * q.2.1 = p.1.map (algebraMap R S) ∧ IsCoprime q.1.1 q.2.1}

variable {m k : ℕ} (p : MonicDegreeEq R (m + k))
variable {S : Type v} [CommRing S] [Algebra R S]
variable {T : Type w} [CommRing T] [Algebra R T]
variable {V : Type z} [CommRing V] [Algebra R V]

/-- Apply an actual coefficient homomorphism to both factors. -/
def map (f : S →ₐ[R] T) (q : CoprimeFactorization S m k p) :
    CoprimeFactorization T m k p :=
  ⟨(q.1.1.map f.toRingHom, q.1.2.map f.toRingHom), by
    constructor
    · change q.1.1.1.map f.toRingHom * q.1.2.1.map f.toRingHom = _
      rw [← Polynomial.map_mul, q.2.1, Polynomial.map_map,
        AlgHom.toRingHom_eq_coe, f.comp_algebraMap]
    · exact q.2.2.map (Polynomial.mapRingHom f.toRingHom)⟩

/-- The first factor is its literal coefficient image. -/
theorem map_fst (f : S →ₐ[R] T) (q : CoprimeFactorization S m k p) :
    (map p f q).1.1 = q.1.1.map f.toRingHom := rfl

/-- The second factor is its literal coefficient image. -/
theorem map_snd (f : S →ₐ[R] T) (q : CoprimeFactorization S m k p) :
    (map p f q).1.2 = q.1.2.map f.toRingHom := rfl

/-- Mapping coefficients by the identity leaves the actual factorization unchanged. -/
theorem map_id (q : CoprimeFactorization S m k p) : map p (AlgHom.id R S) q = q := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> simp [map]

/-- The actual coefficient maps respect composition. -/
theorem map_comp (f : S →ₐ[R] T) (g : T →ₐ[R] V)
    (q : CoprimeFactorization S m k p) :
    map p (g.comp f) q = map p g (map p f q) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [map, Polynomial.map_map, AlgHom.comp_toRingHom]

/-- The original universal algebra's representing equivalence is natural
for the actual coefficient maps on factorizations. -/
theorem homEquiv_comp
    (φ : UniversalCoprimeFactorizationRing m k rfl p →ₐ[R] S) (f : S →ₐ[R] T) :
    UniversalCoprimeFactorizationRing.homEquiv T m k rfl p (f.comp φ) =
      map p f (UniversalCoprimeFactorizationRing.homEquiv S m k rfl p φ) := by
  apply Subtype.ext
  apply Prod.ext
  · exact UniversalCoprimeFactorizationRing.homEquiv_comp_fst S m k rfl p φ f
  · exact UniversalCoprimeFactorizationRing.homEquiv_comp_snd S m k rfl p φ f

section Local

variable [IsLocalRing R]

/-- Actual reduction of both polynomial factors to the residue field. -/
def factorizationReduction (q : CoprimeFactorization R m k p) :
    CoprimeFactorization (ResidueField R) m k p :=
  map p (Algebra.ofId R (ResidueField R)) q

/-- The first reduced polynomial is the original polynomial coefficient reduction. -/
theorem factorizationReduction_fst (q : CoprimeFactorization R m k p) :
    (factorizationReduction p q).1.1.1 = q.1.1.1.map (residue R) := rfl

/-- The second reduced polynomial is the original polynomial coefficient reduction. -/
theorem factorizationReduction_snd (q : CoprimeFactorization R m k p) :
    (factorizationReduction p q).1.2.1 = q.1.2.1.map (residue R) := rfl

/-- Factorization reduction is represented by the original residue composition
on homomorphisms from the universal coprime factorization algebra. -/
theorem factorizationReduction_homEquiv
    (φ : UniversalCoprimeFactorizationRing m k rfl p →ₐ[R] R) :
    factorizationReduction p (UniversalCoprimeFactorizationRing.homEquiv R m k rfl p φ) =
      UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k rfl p
        (HenselianEtaleSections.residueReduction φ) :=
  (homEquiv_comp p φ (Algebra.ofId R (ResidueField R))).symm

/-- Uniqueness of a coprime monic factorization with fixed residues
uses only localness of the base ring. -/
theorem factorizationReduction_injective : Function.Injective (factorizationReduction p) := by
  intro q q' h
  apply (UniversalCoprimeFactorizationRing.homEquiv R m k rfl p).symm.injective
  apply HenselianEtaleLifting.reduction_injective
  apply (UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k rfl p).injective
  rw [← factorizationReduction_homEquiv, ← factorizationReduction_homEquiv,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

end Local

section Henselian

variable [HenselianLocalRing R]

/-- The actual representing equivalences and actual étale residue-point
equivalence construct the factorization equivalence. -/
def factorizationResidueEquiv :
    CoprimeFactorization R m k p ≃ CoprimeFactorization (ResidueField R) m k p :=
  (UniversalCoprimeFactorizationRing.homEquiv R m k rfl p).symm.trans
    ((HenselianEtaleLifting.residueEquiv (UniversalCoprimeFactorizationRing m k rfl p)).trans
      (UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k rfl p))

/-- The equivalence's forward map is precisely coefficient reduction. -/
theorem factorizationResidueEquiv_apply (q : CoprimeFactorization R m k p) :
    factorizationResidueEquiv p q = factorizationReduction p q := by
  change UniversalCoprimeFactorizationRing.homEquiv (ResidueField R) m k rfl p
    (HenselianEtaleSections.residueReduction
      ((UniversalCoprimeFactorizationRing.homEquiv R m k rfl p).symm q)) = _
  rw [← factorizationReduction_homEquiv, Equiv.apply_symm_apply]

/-- Every prescribed coprime monic residue factorization has an actual lift. -/
theorem factorizationReduction_surjective : Function.Surjective (factorizationReduction p) := by
  intro q
  refine ⟨(factorizationResidueEquiv p).symm q, ?_⟩
  rw [← factorizationResidueEquiv_apply, Equiv.apply_symm_apply]

/-- Actual coefficient reduction is bijective on coprime monic factorizations. -/
theorem factorizationReduction_bijective : Function.Bijective (factorizationReduction p) :=
  ⟨factorizationReduction_injective p, factorizationReduction_surjective p⟩

/-- The canonical lifted factorization of exactly the prescribed residue polynomial pair. -/
def lift (q : CoprimeFactorization (ResidueField R) m k p) : CoprimeFactorization R m k p :=
  (factorizationResidueEquiv p).symm q

/-- The lifted factors multiply to the original polynomial over R. -/
theorem lift_mul (q : CoprimeFactorization (ResidueField R) m k p) :
    (lift p q).1.1.1 * (lift p q).1.2.1 = p.1 := by
  simpa using (lift p q).2.1

/-- The lifted factors are coprime over R. -/
theorem lift_isCoprime (q : CoprimeFactorization (ResidueField R) m k p) :
    IsCoprime (lift p q).1.1.1 (lift p q).1.2.1 := (lift p q).2.2

/-- Reducing the lift recovers the given factorization, not just its product. -/
theorem factorizationReduction_lift (q : CoprimeFactorization (ResidueField R) m k p) :
    factorizationReduction p (lift p q) = q := by
  rw [← factorizationResidueEquiv_apply]
  exact (factorizationResidueEquiv p).apply_symm_apply q

/-- The first lifted polynomial has exactly the prescribed coefficient residues. -/
theorem lift_fst_reduction (q : CoprimeFactorization (ResidueField R) m k p) :
    (lift p q).1.1.1.map (residue R) = q.1.1.1 :=
  congrArg (fun q => q.1.1.1) (factorizationReduction_lift p q)

/-- The second lifted polynomial has exactly the prescribed coefficient residues. -/
theorem lift_snd_reduction (q : CoprimeFactorization (ResidueField R) m k p) :
    (lift p q).1.2.1.map (residue R) = q.1.2.1 :=
  congrArg (fun q => q.1.2.1) (factorizationReduction_lift p q)

/-- Lifting the residue of an actual factorization returns that same factorization. -/
theorem lift_factorizationReduction (q : CoprimeFactorization R m k p) :
    lift p (factorizationReduction p q) = q := by
  rw [← factorizationResidueEquiv_apply]
  exact (factorizationResidueEquiv p).symm_apply_apply q

/-- Each specified coprime monic residue factorization has a unique lift,
with the condition expressed by the original coefficient reduction. -/
theorem existsUnique_lift (q : CoprimeFactorization (ResidueField R) m k p) :
    ∃! q' : CoprimeFactorization R m k p, factorizationReduction p q' = q := by
  refine ⟨lift p q, factorizationReduction_lift p q, ?_⟩
  intro q' hq'
  exact factorizationReduction_injective p (hq'.trans (factorizationReduction_lift p q).symm)

/-- Equality of the two actual reduced polynomials identifies any proposed
coprime monic lift with the canonical one. -/
theorem lift_unique (q : CoprimeFactorization (ResidueField R) m k p)
    (q' : CoprimeFactorization R m k p)
    (h₁ : q'.1.1.1.map (residue R) = q.1.1.1)
    (h₂ : q'.1.2.1.map (residue R) = q.1.2.1) : q' = lift p q := by
  apply factorizationReduction_injective p
  rw [factorizationReduction_lift]
  exact Subtype.ext (Prod.ext (Subtype.ext h₁) (Subtype.ext h₂))

end Henselian

end PrimeGap182.TypeIII.HenselianFactorizationLifting

#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.CoprimeFactorization
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.map
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.map_fst
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.map_snd
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.map_id
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.map_comp
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.homEquiv_comp
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_fst
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_snd
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_homEquiv
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_injective
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationResidueEquiv
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationResidueEquiv_apply
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_surjective
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_bijective
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_mul
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_isCoprime
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.factorizationReduction_lift
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_fst_reduction
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_snd_reduction
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_factorizationReduction
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.existsUnique_lift
#print axioms PrimeGap182.TypeIII.HenselianFactorizationLifting.lift_unique
