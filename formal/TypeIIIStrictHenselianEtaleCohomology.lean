import TypeIIIStrictHenselianEtaleSections
import TypeIIIExactResolutionQuasiIso
import TypeIIIRightDerivedPostcompose

/-!
# Actual cohomology over a strictly henselian local base

The proved exactness of the original global-sections functor makes all its
positive derived functors zero. For any scheme over this base, the actual
closed-point stalk of its relative derived image is naturally its global
cohomology. The degree-zero comparison retains the original germ, direct
image, and augmentation maps.

The source of this cohomology is the whole scheme over the local base.
Comparison with the cohomology of its closed fiber is a further theorem.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.StrictHenselianEtaleCohomology

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry IsLocalRing

variable (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
  (E : Type u) [Ring E]

/-- Every sheaf of modules on the actual small étale site has zero
positive cohomology over this strictly henselian local base. -/
theorem isZero_cohomology_succ (n : ℕ)
    (F : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u} E)) :
    IsZero ((EtaleCohomology.functor (Spec (.of R)) E (n + 1)).obj F) :=
  rightDerived_isZero_of_preservesHomology (EtaleCohomology.sections (Spec (.of R)) E) n F

variable {X : Scheme.{u}} (q : X ⟶ Spec (.of R))

/-- Taking global sections of the original relative derived image
gives the actual cohomology of its source scheme. -/
def baseIso (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙ EtaleCohomology.sections (Spec (.of R)) E ≅
      EtaleCohomology.functor X E n :=
  rightDerivedPostcomposeIso (EtaleDirectImage.functor q E)
    (EtaleCohomology.sections X E) (EtaleCohomology.sections (Spec (.of R)) E)
    (EtaleCohomology.directImageIso q E) n

/-- The original ordinary direct-image stalk is actual global sections
of the source, through the original henselian germ comparison. -/
def ordinaryStalkIso :
    EtaleDirectImage.functor q E ⋙
        (Scheme.pointSmallEtale (HenselianEtaleScheme.residueSpec R)).sheafFiber
          (A := ModuleCat.{u} E) ≅
      EtaleCohomology.sections X E :=
  Functor.isoWhiskerLeft (EtaleDirectImage.functor q E)
      (StrictHenselianEtaleSections.stalkIso R E) ≪≫
    EtaleCohomology.directImageIso q E

/-- The actual geometric closed-point stalk of Rⁿq_* is naturally
the global cohomology of the original source scheme. -/
def stalkIso (n : ℕ) :
    EtaleDerivedDirectImage.functor q E n ⋙
        (Scheme.pointSmallEtale (HenselianEtaleScheme.residueSpec R)).sheafFiber
          (A := ModuleCat.{u} E) ≅
      EtaleCohomology.functor X E n :=
  Functor.isoWhiskerLeft (EtaleDerivedDirectImage.functor q E n)
      (StrictHenselianEtaleSections.stalkIso R E) ≪≫
    baseIso R E q n

/-- In degree zero the global comparison commutes with the original
augmentation maps and the original direct-image section comparison. -/
theorem baseIso_zero :
    Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).inv
        (EtaleCohomology.sections (Spec (.of R)) E) ≫ (baseIso R E q 0).hom =
      (EtaleCohomology.directImageIso q E).hom ≫ (EtaleCohomology.zeroIso X E).inv :=
  rightDerivedPostcomposeIso_zero (EtaleDirectImage.functor q E)
    (EtaleCohomology.sections X E) (EtaleCohomology.sections (Spec (.of R)) E)
    (EtaleCohomology.directImageIso q E)

set_option backward.isDefEq.respectTransparency false in
/-- The full stalk comparison in degree zero agrees with the original
ordinary stalk comparison under the two canonical zero isomorphisms. -/
theorem stalkIso_zero :
    Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).inv
        ((Scheme.pointSmallEtale (HenselianEtaleScheme.residueSpec R)).sheafFiber
          (A := ModuleCat.{u} E)) ≫ (stalkIso R E q 0).hom =
      (ordinaryStalkIso R E q).hom ≫ (EtaleCohomology.zeroIso X E).inv := by
  apply NatTrans.ext
  funext F
  have hs := (StrictHenselianEtaleSections.stalkIso R E).hom.naturality
    ((EtaleDerivedDirectImage.zeroIso q E).inv.app F)
  have hb := NatTrans.congr_app (baseIso_zero R E q) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hb
  simp only [stalkIso, ordinaryStalkIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, assoc]
  rw [← assoc, hs, assoc, hb]

set_option backward.isDefEq.respectTransparency false in
/-- Equivalently, transport by the canonical zero isomorphisms gives
precisely the original ordinary stalk-to-global-sections comparison. -/
theorem stalkIso_zero_eq :
    (stalkIso R E q 0).hom =
      Functor.whiskerRight (EtaleDerivedDirectImage.zeroIso q E).hom
          ((Scheme.pointSmallEtale (HenselianEtaleScheme.residueSpec R)).sheafFiber
            (A := ModuleCat.{u} E)) ≫
        (ordinaryStalkIso R E q).hom ≫ (EtaleCohomology.zeroIso X E).inv := by
  let Z := Functor.isoWhiskerRight (EtaleDerivedDirectImage.zeroIso q E)
    ((Scheme.pointSmallEtale (HenselianEtaleScheme.residueSpec R)).sheafFiber
      (A := ModuleCat.{u} E))
  rw [← cancel_epi Z.inv]
  change Z.inv ≫ (stalkIso R E q 0).hom = Z.inv ≫ Z.hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  exact stalkIso_zero R E q

#print axioms isZero_cohomology_succ
#print axioms baseIso
#print axioms ordinaryStalkIso
#print axioms stalkIso
#print axioms baseIso_zero
#print axioms stalkIso_zero
#print axioms stalkIso_zero_eq

end PrimeGap182.TypeIII.StrictHenselianEtaleCohomology
