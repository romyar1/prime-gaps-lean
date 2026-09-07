import TypeIIIHenselianEtaleLifting
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Étale sections through specified residue-field points

Every residue-field point of an étale scheme over a henselian local
ring lifts uniquely to a section over the original ring.  The proof
uses an actual affine open neighborhood and the proved algebraic
lifting theorem.  The scheme itself need not be affine or separated.

Uniqueness already holds over a local ring.  Two proposed sections
with the same residue point factor through one affine neighborhood:
an open subset of the spectrum of a local ring containing its closed
point is the whole spectrum.  Algebraic uniqueness on that common
chart then proves equality of the original scheme morphisms.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.HenselianEtaleScheme

open CategoryTheory AlgebraicGeometry IsLocalRing
open HenselianEtaleSections

variable (R : Type u) [CommRing R]

section Local

variable [IsLocalRing R]

/-- The actual closed-point morphism induced by the residue ring map. -/
def residueSpec : Spec (.of (ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (residue R))

/-- The unique point of the residue-field spectrum maps to the closed point of Spec R. -/
theorem residueSpec_closedPoint :
    residueSpec R (closedPoint (ResidueField R)) = closedPoint R :=
  IsLocalRing.PrimeSpectrum.comap_residue R _

/-- A morphism from a local spectrum factors topologically through
every open immersion whose image contains its closed-point image. -/
theorem range_subset_open_of_closedPoint_mem {X Y : Scheme.{u}}
    (f : Spec (.of R) ⟶ X) (j : Y ⟶ X) [IsOpenImmersion j]
    (h : f (closedPoint R) ∈ Set.range j) : Set.range f ⊆ Set.range j := by
  have htop : f ⁻¹ᵁ j.opensRange = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem f h
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ f ⁻¹ᵁ j.opensRange := by rw [htop]; trivial
  exact hx

end Local

section Affine

variable {R}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Recover the actual algebra homomorphism from an affine morphism
and its commuting triangle over Spec R. -/
def affinePointAlgHom (t : Spec (.of B) ⟶ Spec (.of A))
    (ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) : A →ₐ[R] B := by
  refine ⟨(Spec.preimage t).hom, ?_⟩
  have hw : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage t =
      CommRingCat.ofHom (algebraMap R B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact ht
  intro r
  exact congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of B => h r) hw

/-- Taking Spec of the recovered algebra homomorphism returns the original affine morphism. -/
theorem specMap_affinePointAlgHom (t : Spec (.of B) ⟶ Spec (.of A))
    (ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    Spec.map (CommRingCat.ofHom (affinePointAlgHom t ht).toRingHom) = t :=
  Spec.map_preimage t

/-- Spec of an actual algebra homomorphism satisfies its original base triangle. -/
theorem specMap_algHom_over (φ : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact φ.commutes r

variable [IsLocalRing R]

/-- The proved algebraic residue reduction is exactly restriction of
the corresponding scheme morphism along the actual residue-point map. -/
theorem specMap_residueReduction (φ : A →ₐ[R] R) :
    Spec.map (CommRingCat.ofHom (residueReduction φ).toRingHom) =
      residueSpec R ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  change Spec.map (CommRingCat.ofHom ((residue R).comp φ.toRingHom)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

/-- Affine scheme sections with the same residue restriction agree,
using the actual algebraic reduction-injectivity theorem. -/
theorem affine_section_ext [Algebra.Etale R A]
    (s₁ s₂ : Spec (.of R) ⟶ Spec (.of A))
    (h₁ : s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _)
    (h₂ : s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _)
    (hres : residueSpec R ≫ s₁ = residueSpec R ≫ s₂) : s₁ = s₂ := by
  let φ₁ : A →ₐ[R] R := affinePointAlgHom s₁ (by simpa using h₁)
  let φ₂ : A →ₐ[R] R := affinePointAlgHom s₂ (by simpa using h₂)
  have hφ₁ : Spec.map (CommRingCat.ofHom φ₁.toRingHom) = s₁ :=
    specMap_affinePointAlgHom _ _
  have hφ₂ : Spec.map (CommRingCat.ofHom φ₂.toRingHom) = s₂ :=
    specMap_affinePointAlgHom _ _
  have hred : residueReduction φ₁ = residueReduction φ₂ := by
    have h : CommRingCat.ofHom (residueReduction φ₁).toRingHom =
        CommRingCat.ofHom (residueReduction φ₂).toRingHom := Spec.map_injective (by
      rw [specMap_residueReduction, specMap_residueReduction, hφ₁, hφ₂]
      exact hres)
    ext a
    exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (ResidueField R) => f.hom a) h
  have hφ : φ₁ = φ₂ := HenselianEtaleLifting.reduction_injective hred
  rw [← hφ₁, ← hφ₂, hφ]

end Affine

section AffineHenselian

variable {R} {A : Type u} [CommRing A] [Algebra R A] [HenselianLocalRing R]

/-- A specified residue-field point of an affine étale scheme lifts
to an actual section of its structural morphism. -/
theorem affine_exists_section [Algebra.Etale R A]
    (t : Spec (.of (ResidueField R)) ⟶ Spec (.of A))
    (ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = residueSpec R) :
    ∃ s : Spec (.of R) ⟶ Spec (.of A),
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _ ∧
        residueSpec R ≫ s = t := by
  let φ : A →ₐ[R] ResidueField R := affinePointAlgHom t ht
  obtain ⟨ψ, hψ⟩ := HenselianEtaleLifting.reduction_surjective φ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_, ?_⟩
  · simpa using specMap_algHom_over ψ
  · rw [← specMap_residueReduction, hψ]
    exact specMap_affinePointAlgHom t ht

end AffineHenselian

section SchemeLocal

variable [IsLocalRing R] {U : Scheme.{u}}
variable (q : U ⟶ Spec (.of R)) [Etale q]

/-- Scheme sections of an arbitrary étale scheme over a local ring
are determined by their actual residue-field restriction. -/
theorem section_ext (s₁ s₂ : Spec (.of R) ⟶ U)
    (h₁ : s₁ ≫ q = 𝟙 _) (h₂ : s₂ ≫ q = 𝟙 _)
    (hres : residueSpec R ≫ s₁ = residueSpec R ≫ s₂) : s₁ = s₂ := by
  have hclosed : s₁ (closedPoint R) = s₂ (closedPoint R) := by
    have h := congrArg (fun f => f (closedPoint (ResidueField R))) hres
    change s₁ (residueSpec R (closedPoint (ResidueField R))) =
      s₂ (residueSpec R (closedPoint (ResidueField R))) at h
    rw [residueSpec_closedPoint] at h
    exact h
  obtain ⟨A, j, hj, hxj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := s₁ (closedPoint R)) (U := ⊤) (by trivial)
  let : IsOpenImmersion j := hj
  have hr₁ := range_subset_open_of_closedPoint_mem R s₁ j hxj
  have hr₂ := range_subset_open_of_closedPoint_mem R s₂ j (hclosed ▸ hxj)
  let a₁ := IsOpenImmersion.lift j s₁ hr₁
  let a₂ := IsOpenImmersion.lift j s₂ hr₂
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ q)
  let : Algebra R A := g.hom.toAlgebra
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ q := hg
  let : Algebra.Etale R A := by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp
    rw [hg]
    infer_instance
  have ha₁ : a₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _ := by
    rw [hq, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact h₁
  have ha₂ : a₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _ := by
    rw [hq, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact h₂
  have hared : residueSpec R ≫ a₁ = residueSpec R ≫ a₂ := by
    apply (cancel_mono j).mp
    simpa only [Category.assoc, a₁, a₂, IsOpenImmersion.lift_fac] using hres
  have ha : a₁ = a₂ := affine_section_ext a₁ a₂ ha₁ ha₂ hared
  calc
    s₁ = a₁ ≫ j := (IsOpenImmersion.lift_fac j s₁ hr₁).symm
    _ = a₂ ≫ j := congrArg (fun a => a ≫ j) ha
    _ = s₂ := IsOpenImmersion.lift_fac j s₂ hr₂

end SchemeLocal

section SchemeHenselian

variable [HenselianLocalRing R] {U : Scheme.{u}}
variable (q : U ⟶ Spec (.of R)) [Etale q]

/-- Every specified residue-field point of an arbitrary étale scheme
over a henselian local ring lifts to an actual section. -/
theorem exists_section (t : Spec (.of (ResidueField R)) ⟶ U)
    (ht : t ≫ q = residueSpec R) :
    ∃ s : Spec (.of R) ⟶ U, s ≫ q = 𝟙 _ ∧ residueSpec R ≫ s = t := by
  obtain ⟨A, j, hj, hxj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := t (closedPoint (ResidueField R))) (U := ⊤) (by trivial)
  let : IsOpenImmersion j := hj
  have hrt := range_subset_open_of_closedPoint_mem (ResidueField R) t j hxj
  let tA := IsOpenImmersion.lift j t hrt
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ q)
  let : Algebra R A := g.hom.toAlgebra
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ q := hg
  let : Algebra.Etale R A := by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp
    rw [hg]
    infer_instance
  have htA : tA ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = residueSpec R := by
    rw [hq, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact ht
  obtain ⟨sA, hsA, hresA⟩ := affine_exists_section tA htA
  refine ⟨sA ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hq, hsA]
  · rw [← Category.assoc, hresA]
    exact IsOpenImmersion.lift_fac j t hrt

/-- The actual section lifting the specified residue point is unique.
Neither an affine nor a separated hypothesis is imposed on U. -/
theorem existsUnique_section (t : Spec (.of (ResidueField R)) ⟶ U)
    (ht : t ≫ q = residueSpec R) :
    ∃! s : Spec (.of R) ⟶ U, s ≫ q = 𝟙 _ ∧ residueSpec R ≫ s = t := by
  obtain ⟨s, hs, hsres⟩ := exists_section R q t ht
  refine ⟨s, ⟨hs, hsres⟩, ?_⟩
  intro s' hs'
  exact section_ext R q s' s hs'.1 hs (hs'.2.trans hsres.symm)

/-- The chosen actual section supplied by the proved existence theorem. -/
def sectionLift (t : Spec (.of (ResidueField R)) ⟶ U)
    (ht : t ≫ q = residueSpec R) : Spec (.of R) ⟶ U :=
  (exists_section R q t ht).choose

/-- The constructed morphism is a section of the original structural map. -/
theorem sectionLift_over (t : Spec (.of (ResidueField R)) ⟶ U)
    (ht : t ≫ q = residueSpec R) : sectionLift R q t ht ≫ q = 𝟙 _ :=
  (exists_section R q t ht).choose_spec.1

/-- Its restriction to the residue-field spectrum is the original specified point. -/
theorem sectionLift_residue (t : Spec (.of (ResidueField R)) ⟶ U)
    (ht : t ≫ q = residueSpec R) : residueSpec R ≫ sectionLift R q t ht = t :=
  (exists_section R q t ht).choose_spec.2

end SchemeHenselian

end PrimeGap182.TypeIII.HenselianEtaleScheme

#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.residueSpec
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.residueSpec_closedPoint
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.range_subset_open_of_closedPoint_mem
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.affinePointAlgHom
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.specMap_affinePointAlgHom
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.specMap_algHom_over
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.specMap_residueReduction
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.affine_section_ext
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.affine_exists_section
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.section_ext
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.exists_section
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.existsUnique_section
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.sectionLift
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.sectionLift_over
#print axioms PrimeGap182.TypeIII.HenselianEtaleScheme.sectionLift_residue
