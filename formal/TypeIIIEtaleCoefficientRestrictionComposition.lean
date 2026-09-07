import TypeIIIEtaleCoefficientRestriction

/-!
# Composition of actual coefficient restriction

On an arbitrary small étale site, restriction along a composite ring
homomorphism is canonically isomorphic to successive restrictions.
The comparison uses the existing module comparison on each original
section module and is the identity on its elements.  On affine schemes
it is the same comparison already used for Artin–Schreier coefficient
maps.  The coefficient rings and their homomorphisms are arbitrary.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleCoefficientRestriction

open CategoryTheory AlgebraicGeometry

variable (S : Scheme.{u})
  {E₀ E₁ E₂ : Type u} [Ring E₀] [Ring E₁] [Ring E₂]
  (f : E₀ →+* E₁) (g : E₁ →+* E₂) (gf : E₀ →+* E₂) (hgf : gf = g.comp f)

/-- The original module composition comparison, applied to each
section of the original sheaf. -/
def compIso' : functor S gf ≅ functor S g ⋙ functor S f :=
  NatIso.ofComponents (fun F =>
    ObjectProperty.isoMk _
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsComp' f g gf hgf)))
    (by intro F G a; apply Sheaf.hom_ext; ext U x; rfl)

/-- Every forward component is the existing module comparison. -/
theorem compIso'_hom_app_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E₂)) (U : S.Etaleᵒᵖ) :
    ((compIso' S f g gf hgf).hom.app F).hom.app U =
      (ModuleCat.restrictScalarsComp' f g gf hgf).hom.app (F.obj.obj U) := rfl

/-- Every inverse component is the inverse of the same module comparison. -/
theorem compIso'_inv_app_hom_app
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E₂)) (U : S.Etaleᵒᵖ) :
    ((compIso' S f g gf hgf).inv.app F).hom.app U =
      (ModuleCat.restrictScalarsComp' f g gf hgf).inv.app (F.obj.obj U) := rfl

/-- The forward comparison keeps each original section unchanged. -/
theorem compIso'_hom_app_apply
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E₂)) (U : S.Etaleᵒᵖ)
    (x : F.obj.obj U) :
    ((compIso' S f g gf hgf).hom.app F).hom.app U x = x := rfl

/-- The inverse comparison also keeps each original section unchanged. -/
theorem compIso'_inv_app_apply
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E₂)) (U : S.Etaleᵒᵖ)
    (x : F.obj.obj U) :
    ((compIso' S f g gf hgf).inv.app F).hom.app U x = x := rfl

/-- Composition with the literal composite ring homomorphism. -/
abbrev compIso : functor S (g.comp f) ≅ functor S g ⋙ functor S f :=
  compIso' S f g (g.comp f) rfl

section Affine

variable (R : Type u) [CommRing R]
  {D₀ D₁ D₂ : Type u} [CommRing D₀] [CommRing D₁] [CommRing D₂]
  (a : D₀ →+* D₁) (b : D₁ →+* D₂)

/-- On the original affine site this is the existing Artin–Schreier
coefficient-restriction composition isomorphism. -/
theorem compIso_affine :
    compIso (Spec (.of R)) a b = etaleModuleCoefficientRestrictionCompIso R a b := rfl

end Affine

#print axioms compIso'
#print axioms compIso'_hom_app_hom_app
#print axioms compIso'_inv_app_hom_app
#print axioms compIso'_hom_app_apply
#print axioms compIso'_inv_app_apply
#print axioms compIso
#print axioms compIso_affine

end PrimeGap182.TypeIII.EtaleCoefficientRestriction
