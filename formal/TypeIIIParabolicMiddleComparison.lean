import TypeIIIPublishedPhysicalConstruction

/-!
# Identifying the parabolic image from boundary exact sequences

This is the algebraic comparison needed for the compact cohomology of
the middle extension. A compact-to-ordinary map factors through a middle
object. Exactness at that object, and vanishing of the incoming/outgoing
boundary maps, make the factors surjective/injective. The middle object
is therefore canonically the image of the ORIGINAL comparison map.

The final construction applies this criterion to the existing parabolic
core under exact stalk pullback. Both natural maps are preserved. It does
not provide the geometric boundary sequences or prove their vanishing
for the intended sheaf; those remain realization obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.ParabolicMiddleComparison

universe u v w z
variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R}

/-- The two exact boundary sequences and their original comparison map.
There is no stipulated image isomorphism, rank, or Fourier conclusion. -/
structure BoundaryFactorization (f : X ⟶ Y) where
  middle : ModuleCat.{v} R
  leftBoundary : ModuleCat.{v} R
  rightBoundary : ModuleCat.{v} R
  fromCompact : X ⟶ middle
  toOrdinary : middle ⟶ Y
  fromBoundary : leftBoundary ⟶ middle
  toBoundary : middle ⟶ rightBoundary
  factorization : fromCompact ≫ toOrdinary = f
  left_exact : LinearMap.range fromBoundary.hom = LinearMap.ker toOrdinary.hom
  right_exact : LinearMap.range fromCompact.hom = LinearMap.ker toBoundary.hom

variable {f : X ⟶ Y} (D : BoundaryFactorization f)
  (hleft : D.fromBoundary.hom = 0) (hright : D.toBoundary.hom = 0)

include hright in
theorem fromCompact_surjective : Function.Surjective D.fromCompact.hom := by
  apply LinearMap.range_eq_top.mp
  simpa only [hright, LinearMap.ker_zero] using D.right_exact

include hleft in
theorem toOrdinary_injective : Function.Injective D.toOrdinary.hom := by
  apply LinearMap.ker_eq_bot.mp
  simpa only [hleft, LinearMap.range_zero] using D.left_exact.symm

/-- Canonical identification obtained from the two exact sequences. -/
def imageIsoMiddle : Abelian.image f ≅ D.middle := by
  letI : Epi D.fromCompact := (ModuleCat.epi_iff_surjective _).mpr
    (fromCompact_surjective D hright)
  letI : Mono D.toOrdinary := (ModuleCat.mono_iff_injective _).mpr
    (toOrdinary_injective D hleft)
  letI : StrongEpi D.fromCompact := strongEpi_of_epi _
  exact Abelian.imageIsoImage f ≪≫
    (Limits.image.isoStrongEpiMono D.fromCompact D.toOrdinary D.factorization).symm

/-- The isomorphism preserves the original inclusion into ordinary cohomology. -/
theorem imageIsoMiddle_hom_toOrdinary :
    (imageIsoMiddle D hleft hright).hom ≫ D.toOrdinary = Abelian.image.ι f := by
  let _ : Epi D.fromCompact := (ModuleCat.epi_iff_surjective _).mpr
    (fromCompact_surjective D hright)
  let _ : Mono D.toOrdinary := (ModuleCat.mono_iff_injective _).mpr
    (toOrdinary_injective D hleft)
  let _ : StrongEpi D.fromCompact := strongEpi_of_epi _
  simp only [imageIsoMiddle, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Limits.image.isoStrongEpiMono_inv_comp_mono, Abelian.imageIsoImage_hom_comp_image_ι]

/-- It also preserves the original map out of compact cohomology. -/
theorem factorThruImage_imageIsoMiddle_hom :
    Abelian.factorThruImage f ≫ (imageIsoMiddle D hleft hright).hom = D.fromCompact := by
  let _ : Mono D.toOrdinary := (ModuleCat.mono_iff_injective _).mpr
    (toOrdinary_injective D hleft)
  apply (cancel_mono D.toOrdinary).mp
  rw [Category.assoc, imageIsoMiddle_hom_toOrdinary, Abelian.image.fac, D.factorization]

section ActualCore

open PublishedPhysicalConstruction

variable {Input : Type u} {C : Type w} [Category.{z} C] [Abelian C]
  (H : CohomologyData Input C) (F : C ⥤ ModuleCat.{w} ℂ)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : Input) (B : BoundaryFactorization (F.map (H.comparison A)))
  (hleft : B.fromBoundary.hom = 0) (hright : B.toBoundary.hom = 0)

/-- The SAME existing parabolic core is identified with the middle object;
exact stalk pullback supplies the categorical-image comparison. -/
def coreStalkMiddleIso : F.obj (parabolicCore H A) ≅ B.middle :=
  coreStalkImageIso H F A ≪≫ imageIsoMiddle B hleft hright

theorem coreStalkMiddleIso_hom_toOrdinary :
    (coreStalkMiddleIso H F A B hleft hright).hom ≫ B.toOrdinary =
      F.map (Abelian.image.ι (H.comparison A)) := by
  simp only [coreStalkMiddleIso, Iso.trans_hom, Category.assoc,
    imageIsoMiddle_hom_toOrdinary, coreStalkImageIso, Abelian.PreservesImage.iso_hom_ι]

theorem fromCompact_coreStalkMiddleIso_hom :
    F.map (Abelian.factorThruImage (H.comparison A)) ≫
      (coreStalkMiddleIso H F A B hleft hright).hom = B.fromCompact := by
  simp only [coreStalkMiddleIso, Iso.trans_hom, ← Category.assoc, coreStalkImageIso,
    Abelian.PreservesImage.factorThruImage_iso_hom, factorThruImage_imageIsoMiddle_hom]

/-- Any compatible actions commute with the canonical comparison. Applying
this for each inertia element (or Frobenius) gives equivariance once the
geometric maps and their naturality have been instantiated. -/
theorem coreStalkMiddleIso_natural
    (a : F.obj (H.compact A) ⟶ F.obj (H.compact A))
    (b : F.obj (parabolicCore H A) ⟶ F.obj (parabolicCore H A))
    (c : B.middle ⟶ B.middle)
    (hab : a ≫ F.map (Abelian.factorThruImage (H.comparison A)) =
      F.map (Abelian.factorThruImage (H.comparison A)) ≫ b)
    (hac : a ≫ B.fromCompact = B.fromCompact ≫ c) :
    b ≫ (coreStalkMiddleIso H F A B hleft hright).hom =
      (coreStalkMiddleIso H F A B hleft hright).hom ≫ c := by
  apply (cancel_epi (F.map (Abelian.factorThruImage (H.comparison A)))).mp
  rw [← Category.assoc, ← hab, Category.assoc, fromCompact_coreStalkMiddleIso_hom,
    ← Category.assoc, fromCompact_coreStalkMiddleIso_hom, hac]

end ActualCore
end PrimeGap182.TypeIII.ParabolicMiddleComparison

#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.fromCompact_surjective
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.toOrdinary_injective
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.imageIsoMiddle
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.imageIsoMiddle_hom_toOrdinary
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.factorThruImage_imageIsoMiddle_hom
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.coreStalkMiddleIso
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.coreStalkMiddleIso_hom_toOrdinary
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.fromCompact_coreStalkMiddleIso_hom
#print axioms PrimeGap182.TypeIII.ParabolicMiddleComparison.coreStalkMiddleIso_natural
