import TypeIIIEtaleCompactSupportCoefficientRestriction
import TypeIIIEtaleDerivedCoefficientComposition
import TypeIIIEtaleExtensionCoefficientComposition

/-!
# Composition of the original compact-support coefficient comparisons

The original comparison for the composite Rⁿq_* j_! respects successive
coefficient restrictions.  Its two original factors are used: derived
direct-image coherence is combined with naturality and the original
extension comparison.  The mixed inverse formula is an algebraic
consequence for these same isomorphisms.

The scheme morphism and coefficient rings are arbitrary.  This is a
coefficient-category coherence statement for the existing functors.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction

open CategoryTheory CategoryTheory.Category AlgebraicGeometry

variable {X S : Scheme.{u}} (q : X ⟶ S) (U : X.Etale)
  {E₀ E₁ E₂ : Type u} [Ring E₀] [Ring E₁] [Ring E₂]
  (f : E₀ →+* E₁) (g : E₁ →+* E₂) (gf : E₀ →+* E₂)
  (hgf : gf = g.comp f) (n : ℕ)

/-- Successive original compact-support coefficient comparisons agree
with the comparison for the specified composite, using the original
scalar composition maps on both sites. -/
theorem iso_comp'
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleCoefficientRestriction.compIso' S f g gf hgf).hom.app
          ((EtaleExtensionByZero.functor X U E₂ ⋙
            EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (EtaleCoefficientRestriction.functor S f).map ((iso q U g n).hom.app F) ≫
        (iso q U f n).hom.app ((EtaleCoefficientRestriction.functor U.left g).obj F) =
      (iso q U gf n).hom.app F ≫
        (EtaleExtensionByZero.functor X U E₀ ⋙
          EtaleDerivedDirectImage.functor q E₀ n).map
            ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).hom.app F) := by
  simp only [iso_hom_app, Functor.map_comp, Functor.comp_map, assoc]
  have hν := (EtaleCoefficientRestriction.derivedDirectImageMap q f n).naturality
    ((EtaleExtensionCoefficientRestriction.iso X U g).hom.app F)
  have hν' := congrArg
    (fun z => z ≫ (EtaleDerivedDirectImage.functor q E₀ n).map
      ((EtaleExtensionCoefficientRestriction.iso X U f).hom.app
        ((EtaleCoefficientRestriction.functor U.left g).obj F))) hν
  simp only [Functor.comp_map, assoc] at hν'
  erw [hν']
  have hδ := EtaleCoefficientRestriction.derivedDirectImageMap_comp'
    q f g gf hgf n ((EtaleExtensionByZero.functor X U E₂).obj F)
  have hδ' := congrArg
    (fun z => z ≫
      (EtaleDerivedDirectImage.functor q E₀ n).map
        ((EtaleCoefficientRestriction.functor X f).map
          ((EtaleExtensionCoefficientRestriction.iso X U g).hom.app F)) ≫
      (EtaleDerivedDirectImage.functor q E₀ n).map
        ((EtaleExtensionCoefficientRestriction.iso X U f).hom.app
          ((EtaleCoefficientRestriction.functor U.left g).obj F))) hδ
  simp only [assoc] at hδ'
  erw [hδ']
  have hξ := congrArg (EtaleDerivedDirectImage.functor q E₀ n).map
    (EtaleExtensionCoefficientRestriction.iso_comp' X U f g gf hgf F)
  simp only [Functor.map_comp] at hξ
  erw [hξ]

/-- Coherence for the literal composite coefficient homomorphism. -/
theorem iso_comp
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleCoefficientRestriction.compIso S f g).hom.app
          ((EtaleExtensionByZero.functor X U E₂ ⋙
            EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (EtaleCoefficientRestriction.functor S f).map ((iso q U g n).hom.app F) ≫
        (iso q U f n).hom.app ((EtaleCoefficientRestriction.functor U.left g).obj F) =
      (iso q U (g.comp f) n).hom.app F ≫
        (EtaleExtensionByZero.functor X U E₀ ⋙
          EtaleDerivedDirectImage.functor q E₀ n).map
            ((EtaleCoefficientRestriction.compIso U.left f g).hom.app F) :=
  iso_comp' q U f g (g.comp f) rfl n F

/-- The mixed inverse form retains the original inverse comparisons;
it is useful when a finite coefficient transition is restricted to a
common coefficient category. -/
theorem iso_inv_comp'_hom
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleCoefficientRestriction.functor S f).map ((iso q U g n).inv.app F) ≫
        (EtaleCoefficientRestriction.compIso' S f g gf hgf).inv.app
          ((EtaleExtensionByZero.functor X U E₂ ⋙
            EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (iso q U gf n).hom.app F =
      (iso q U f n).hom.app ((EtaleCoefficientRestriction.functor U.left g).obj F) ≫
        (EtaleExtensionByZero.functor X U E₀ ⋙
          EtaleDerivedDirectImage.functor q E₀ n).map
            ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).inv.app F) := by
  let eA := (EtaleCoefficientRestriction.compIso' S f g gf hgf).app
    ((EtaleExtensionByZero.functor X U E₂ ⋙
      EtaleDerivedDirectImage.functor q E₂ n).obj F)
  let eB := (EtaleCoefficientRestriction.functor S f).mapIso ((iso q U g n).app F)
  let eC := (iso q U f n).app ((EtaleCoefficientRestriction.functor U.left g).obj F)
  let eD := (iso q U gf n).app F
  let eE := (EtaleExtensionByZero.functor X U E₀ ⋙
    EtaleDerivedDirectImage.functor q E₀ n).mapIso
      ((EtaleCoefficientRestriction.compIso' U.left f g gf hgf).app F)
  have h : eA.hom ≫ eB.hom ≫ eC.hom = eD.hom ≫ eE.hom :=
    iso_comp' q U f g gf hgf n F
  have h' := congrArg (fun z => eB.inv ≫ eA.inv ≫ z ≫ eE.inv) h
  simp only [assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id] at h'
  exact h'.symm

/-- The mixed inverse form for the literal composite coefficient map. -/
theorem iso_inv_comp_hom
    (F : Sheaf U.left.smallEtaleTopology (ModuleCat.{u} E₂)) :
    (EtaleCoefficientRestriction.functor S f).map ((iso q U g n).inv.app F) ≫
        (EtaleCoefficientRestriction.compIso S f g).inv.app
          ((EtaleExtensionByZero.functor X U E₂ ⋙
            EtaleDerivedDirectImage.functor q E₂ n).obj F) ≫
        (iso q U (g.comp f) n).hom.app F =
      (iso q U f n).hom.app ((EtaleCoefficientRestriction.functor U.left g).obj F) ≫
        (EtaleExtensionByZero.functor X U E₀ ⋙
          EtaleDerivedDirectImage.functor q E₀ n).map
            ((EtaleCoefficientRestriction.compIso U.left f g).inv.app F) :=
  iso_inv_comp'_hom q U f g (g.comp f) rfl n F

#print axioms iso_comp'
#print axioms iso_comp
#print axioms iso_inv_comp'_hom
#print axioms iso_inv_comp_hom

end PrimeGap182.TypeIII.EtaleCompactSupportCoefficientRestriction
