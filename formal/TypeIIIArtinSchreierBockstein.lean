import TypeIIIArtinSchreierCoefficientGenerator
import TypeIIIAlgebraicallyClosedEtalePoints
import TypeIIIArtinSchreierLimitSheaf
import TypeIIITorsionCoefficientExactness
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The original coefficient-reduction short exact sequence

At every geometric point, the actual projected identity section compares
the original character coefficient map with the literal coefficient-ring
map. Exact scalar kernels therefore give exactness of the actual sheaf
sequence. In particular, reduction from the actual coefficient limit to
level n is the cokernel of multiplication by ell^(n+1), which is a
monomorphism.

This is a short exact sequence of ordinary module sheaves. No interchange
of inverse limits and derived images, or adic cohomology comparison, is
asserted.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ScalarSequence

variable {E E' : Type u} [CommRing E] [CommRing E']
  (r : E →+* E') (N : ℕ) (hN : (N : E') = 0)

/-- The scalar sequence uses multiplication by the integer and the
literal original coefficient ring map. -/
def coefficientRingSequence : ShortComplex (ModuleCat.{u} E) :=
  ShortComplex.mk (N • 𝟙 (ModuleCat.of E E)) (coefficientRingModuleMap r) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change r (N • x) = 0
    rw [nsmul_eq_mul, map_mul, map_natCast, hN, zero_mul])

/-- Exactness and regularity of the actual scalar quotient give its
short exact sequence in the original module category. -/
theorem coefficientRingSequence_shortExact
    (hker : ∀ x : E, r x = 0 ↔ (N : E) ∣ x)
    (hinj : Function.Injective (fun x : E => (N : E) * x))
    (hsurj : Function.Surjective r) :
    (coefficientRingSequence r N hN).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (hker x).mp hx
    refine ⟨a, ?_⟩
    change N • a = x
    simpa only [nsmul_eq_mul] using ha.symm
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun x : E => N • x)
    simpa only [nsmul_eq_mul] using hinj
  · exact (ModuleCat.epi_iff_surjective _).mpr hsurj

end ScalarSequence

section CharacterSequence

variable (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
  (f : R) {E E' : Type u} [CommRing E] [CommRing E']
  [Invertible (p : E)] [Invertible (p : E')]
  (ψ : AddChar (ZMod p) E) (ψ' : AddChar (ZMod p) E')
  (r : E →+* E') (N : ℕ) (hN : (N : E') = 0)

/-- The sheaf sequence uses the original character-image coefficient
map, with multiplication on its original source sheaf. -/
def artinSchreierCoefficientSequence :
    ShortComplex (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)) :=
  ShortComplex.mk
    (N • 𝟙 (artinSchreierRingCharacterImageSheaf p f E ψ))
    (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r) (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r).hom.app U
        (N • x) = 0
      rw [map_nsmul]
      let y : (artinSchreierRingCharacterImageSheaf p f E' ψ').obj.obj U :=
        (artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r).hom.app U x
      have hy : (N : E') • y = 0 := by rw [hN, zero_smul]
      simpa only [Nat.cast_smul_eq_nsmul] using hy)

variable (hψ : ∀ a, r (ψ a) = ψ' a)

include hψ

/-- The actual generator germs identify the stalk sequence with the
original scalar sequence. The third component is the original scalar
restriction comparison, following restriction of the target generator. -/
def artinSchreierCoefficientSequence_stalkIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (q : Spec (.of Ω) ⟶ Spec (.of R))
    (t : (Scheme.pointSmallEtale q).fiber.obj (artinSchreierEtaleObject p f)) :
    coefficientRingSequence r N hN ≅
      (artinSchreierCoefficientSequence p f ψ ψ' r N hN).map
        (Scheme.pointSmallEtale q).sheafFiber := by
  let g := Spec.preimage q
  have hq : Spec.map g = q := Spec.map_preimage q
  rw [← hq] at t ⊢
  let : Algebra R Ω := g.hom.toAlgebra
  let : CharP Ω p := artinSchreierPointField_charP p R Ω
  let : Algebra (ZMod p) Ω := (ZMod.castHom (dvd_refl p) Ω).toAlgebra
  let Φ := Scheme.pointSmallEtale (Spec.map g)
  let Y := artinSchreierEtaleObject p f
  let L := artinSchreierRingCharacterImageSheaf p f E ψ
  let L' := artinSchreierRingCharacterImageSheaf p f E' ψ'
  let M := ModuleCat.restrictScalars r
  let c := artinSchreierRingCharacterSheafCoefficientMap p f ψ ψ' r
  let e₀ := artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
    Φ.toPresheafFiber Y t L.obj
  let e₀' := artinSchreierRingCharacterIdentitySectionMap p f E' ψ' ≫
    Φ.toPresheafFiber Y t L'.obj
  let : IsIso e₀ :=
    artinSchreierRingCharacterIdentitySectionMap_stalk_isIso p R Ω Ω f E ψ t
  let : IsIso e₀' :=
    artinSchreierRingCharacterIdentitySectionMap_stalk_isIso p R Ω Ω f E' ψ' t
  let e := asIso e₀
  let e' := asIso e₀'
  let d := (Φ.sheafFiberCompIso M).app L'
  let e₃ := M.mapIso e' ≪≫ d.symm
  refine ShortComplex.isoMk e e e₃ ?_ ?_
  · change (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
      Φ.toPresheafFiber Y t L.obj) ≫ Φ.presheafFiber.map ((N • 𝟙 L).hom) =
      (N • 𝟙 (ModuleCat.of E E)) ≫
        (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
          Φ.toPresheafFiber Y t L.obj)
    rw [Category.assoc, Φ.toPresheafFiber_naturality]
    change artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
      (N • 𝟙 (L.obj.obj (op Y))) ≫ Φ.toPresheafFiber Y t L.obj =
      (N • 𝟙 (ModuleCat.of E E)) ≫
        (artinSchreierRingCharacterIdentitySectionMap p f E ψ ≫
          Φ.toPresheafFiber Y t L.obj)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Φ.toPresheafFiber Y t L.obj
        (N • artinSchreierRingCharacterIdentitySectionMap p f E ψ a) =
      Φ.toPresheafFiber Y t L.obj
        (artinSchreierRingCharacterIdentitySectionMap p f E ψ (N • a))
    exact congrArg (Φ.toPresheafFiber Y t L.obj)
      (map_nsmul (artinSchreierRingCharacterIdentitySectionMap p f E ψ).hom N a).symm
  · change e.hom ≫ Φ.sheafFiber.map c =
      coefficientRingModuleMap r ≫ M.map e'.hom ≫ d.inv
    have h : e.hom ≫ Φ.sheafFiber.map c ≫ d.hom =
        coefficientRingModuleMap r ≫ M.map e'.hom :=
      artinSchreierRingCharacterSheafCoefficientMap_stalk_generator p f ψ ψ' r hψ Φ t
    have H := congrArg (fun v => v ≫ d.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using H

/-- Scalar exactness gives stalk exactness at every actual geometric
point; existence of a lift follows from algebraic closedness. -/
theorem artinSchreierCoefficientSequence_geometric_stalk_shortExact
    (hker : ∀ x : E, r x = 0 ↔ (N : E) ∣ x)
    (hinj : Function.Injective (fun x : E => (N : E) * x))
    (hsurj : Function.Surjective r)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (q : Spec (.of Ω) ⟶ Spec (.of R)) :
    ((artinSchreierCoefficientSequence p f ψ ψ' r N hN).map
      (Scheme.pointSmallEtale q).sheafFiber).ShortExact := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective q
  let : Algebra R Ω := g.hom.toAlgebra
  let : CharP Ω p := artinSchreierPointField_charP p R Ω
  obtain ⟨t⟩ := artinSchreierPointSiteFiber_nonempty p R Ω Ω f
  exact ShortComplex.shortExact_of_iso
    (artinSchreierCoefficientSequence_stalkIso p f ψ ψ' r N hN hψ Ω (Spec.map g) t)
    (coefficientRingSequence_shortExact r N hN hker hinj hsurj)

/-- The proved conservative family of actual algebraic-closure points
detects short exactness of the original character coefficient sequence. -/
theorem artinSchreierCoefficientSequence_shortExact
    (hker : ∀ x : E, r x = 0 ↔ (N : E) ∣ x)
    (hinj : Function.Injective (fun x : E => (N : E) * x))
    (hsurj : Function.Surjective r) :
    (artinSchreierCoefficientSequence p f ψ ψ' r N hN).ShortExact := by
  let S := Spec (.of R)
  apply (((algebraicClosureEtalePoints_isConservative S).jointlyReflectIsomorphisms
    (ModuleCat.{u} E)).shortExact_iff
      (artinSchreierCoefficientSequence p f ψ ψ' r N hN)).mpr
  rintro ⟨_, ⟨s⟩⟩
  exact artinSchreierCoefficientSequence_geometric_stalk_shortExact
    p f ψ ψ' r N hN hψ hker hinj hsurj
    (AlgebraicClosure (S.residueField s)) (algebraicClosureEtalePointMap S s)

end CharacterSequence

section LimitCoefficients

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
  {R : Type} [CommRing R] [CharP R p] (f : R)

/-- The original limit-coefficient character sheaf, its integer
multiplication, and its original finite-level reduction form this short
complex. -/
def limitArtinSchreierBocksteinSequence (n : ℕ) :
    ShortComplex (Sheaf (Spec (.of R)).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell))) :=
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  artinSchreierCoefficientSequence p f
    (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
    (torsionCoefficientLimitProjection p ell n) (ell ^ (n + 1))
    (CharP.cast_eq_zero (TorsionCoefficientRing p ell n) (ell ^ (n + 1)))

/-- Its first map is literally the stated multiplication on the
original limit-coefficient sheaf. -/
@[simp] theorem limitArtinSchreierBocksteinSequence_f (n : ℕ) :
    (limitArtinSchreierBocksteinSequence p ell hne f n).f =
      (ell ^ (n + 1)) • 𝟙 (limitArtinSchreierSheaf p ell hne f) := rfl

/-- Its second map is the unchanged original coefficient reduction. -/
@[simp] theorem limitArtinSchreierBocksteinSequence_g (n : ℕ) :
    (limitArtinSchreierBocksteinSequence p ell hne f n).g =
      limitArtinSchreierReduction p ell hne f n := rfl

/-- The original limit-to-finite coefficient sequence is short exact.
The scalar kernel, surjectivity and regularity are proved properties of
the existing coefficient rings, with no extra sheaf hypothesis. -/
theorem limitArtinSchreierBocksteinSequence_shortExact (n : ℕ) :
    (limitArtinSchreierBocksteinSequence p ell hne f n).ShortExact := by
  let : Invertible (p : TorsionCoefficientLimit p ell) :=
    torsionCoefficientLimitPInvertible p ell hne
  let : Invertible (p : TorsionCoefficientRing p ell n) :=
    (torsionCoefficient_p_isUnit p ell n hne).invertible
  apply artinSchreierCoefficientSequence_shortExact
    p f (torsionCoefficientLimitChar p ell) (torsionCoefficientChar p ell n)
    (torsionCoefficientLimitProjection p ell n) (ell ^ (n + 1))
    (CharP.cast_eq_zero (TorsionCoefficientRing p ell n) (ell ^ (n + 1)))
    (torsionCoefficientLimitProjection_char p ell n)
  · intro x
    simpa only [Nat.cast_pow] using
      torsionCoefficientLimitProjection_eq_zero_iff p ell n x
  · simpa only [Nat.cast_pow] using
      torsionCoefficientLimit_mul_ell_pow_injective p ell (n + 1)
  · exact torsionCoefficientLimitProjection_surjective p ell n

end LimitCoefficients

#print axioms coefficientRingSequence
#print axioms coefficientRingSequence_shortExact
#print axioms artinSchreierCoefficientSequence
#print axioms artinSchreierCoefficientSequence_stalkIso
#print axioms artinSchreierCoefficientSequence_geometric_stalk_shortExact
#print axioms artinSchreierCoefficientSequence_shortExact
#print axioms limitArtinSchreierBocksteinSequence
#print axioms limitArtinSchreierBocksteinSequence_f
#print axioms limitArtinSchreierBocksteinSequence_g
#print axioms limitArtinSchreierBocksteinSequence_shortExact

end PrimeGap182.TypeIII
