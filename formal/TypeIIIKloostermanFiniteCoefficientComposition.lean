import TypeIIIKloostermanFiniteCoefficientTransitions

/-!
# Composition in the original finite coefficient categories

The independently defined finite-coefficient Kloosterman transitions
compose with the original scalar-restriction composition isomorphism.
The proof uses the original finite sheaf reductions, naturality of the
original inverse coefficient comparison, and the proved composition
law for that comparison.  It does not use the common-coefficient tower.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category AlgebraicGeometry

attribute [local instance] kloostermanPhaseRing_charP

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The original transitions compose before restriction to the common
coefficient ring, with the original scalar-composition comparison. -/
theorem kloostermanFiniteCoefficientReduction_comp (d : ℕ) {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) :
    kloostermanFiniteCoefficientReduction p ell hne d hmn ≫
        (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
          (torsionCoefficientReduce p ell hmn)).map
            (kloostermanFiniteCoefficientReduction p ell hne d hkm) =
      kloostermanFiniteCoefficientReduction p ell hne d (hkm.trans hmn) ≫
        (EtaleCoefficientRestriction.compIso' (Spec (.of (Polynomial (ZMod p))))
          (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
          (torsionCoefficientReduce p ell (hkm.trans hmn))
          (torsionCoefficientReduce_comp p ell hkm hmn).symm).hom.app
            (kloostermanFiniteCoefficientDerivedImage p ell hne d k) := by
  let F := torsionArtinSchreierSheaf p ell hne k (kloostermanPhaseFunction p)
  let cS := (EtaleCoefficientRestriction.compIso' (Spec (.of (Polynomial (ZMod p))))
    (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
    (torsionCoefficientReduce p ell (hkm.trans hmn))
    (torsionCoefficientReduce_comp p ell hkm hmn).symm).app
      (kloostermanFiniteCoefficientDerivedImage p ell hne d k)
  let cg := (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
    (torsionCoefficientReduce p ell hmn)).mapIso
      ((kloostermanCompactifiedCoefficientIso p (torsionCoefficientReduce p ell hkm) d).app F)
  let cf := (kloostermanCompactifiedCoefficientIso p
    (torsionCoefficientReduce p ell hmn) d).app
      ((EtaleCoefficientRestriction.functor (kloostermanPhaseScheme p)
        (torsionCoefficientReduce p ell hkm)).obj F)
  let cgf := (kloostermanCompactifiedCoefficientIso p
    (torsionCoefficientReduce p ell (hkm.trans hmn)) d).app F
  let cU := (kloostermanCompactifiedDerivedImage p (TorsionCoefficientRing p ell n) d).mapIso
    ((EtaleCoefficientRestriction.compIso' (kloostermanPhaseScheme p)
      (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
      (torsionCoefficientReduce p ell (hkm.trans hmn))
      (torsionCoefficientReduce_comp p ell hkm hmn).symm).app F)
  have hc : cS.hom ≫ cg.hom ≫ cf.hom = cgf.hom ≫ cU.hom :=
    EtaleCompactSupportCoefficientRestriction.iso_comp'
      (kloostermanCompactificationProjection p) (kloostermanCompactificationEtaleObject p)
      (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
      (torsionCoefficientReduce p ell (hkm.trans hmn))
      (torsionCoefficientReduce_comp p ell hkm hmn).symm d F
  have hci : cU.hom ≫ cf.inv ≫ cg.inv = cgf.inv ≫ cS.hom := by
    have h := congrArg (fun z => cgf.inv ≫ z ≫ cf.inv ≫ cg.inv) hc
    simp only [assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Iso.inv_hom_id_assoc, comp_id] at h
    exact h.symm
  have hν := (kloostermanCompactifiedCoefficientIso p
    (torsionCoefficientReduce p ell hmn) d).inv.naturality
      (torsionArtinSchreierReduction p ell hne (kloostermanPhaseFunction p) hkm)
  have hν' := congrArg (fun z => z ≫ cg.inv) hν
  simp only [Functor.comp_map, assoc] at hν'
  have hr := congrArg
    (kloostermanCompactifiedDerivedImage p (TorsionCoefficientRing p ell n) d).map
    (torsionArtinSchreierReduction_comp p ell hne (kloostermanPhaseFunction p) hkm hmn)
  have hr' := congrArg (fun z => z ≫ cf.inv ≫ cg.inv) hr
  simp only [Functor.map_comp, assoc] at hr'
  simp only [kloostermanFiniteCoefficientReduction, Functor.map_comp, assoc]
  erw [← hν', hr', hci]
  rfl

/-- The direct original transition is the successive original
transitions followed by the inverse scalar-composition comparison. -/
theorem kloostermanFiniteCoefficientReduction_eq_comp_restrictScalars
    (d : ℕ) {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    kloostermanFiniteCoefficientReduction p ell hne d (hkm.trans hmn) =
      kloostermanFiniteCoefficientReduction p ell hne d hmn ≫
        (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
          (torsionCoefficientReduce p ell hmn)).map
            (kloostermanFiniteCoefficientReduction p ell hne d hkm) ≫
        (EtaleCoefficientRestriction.compIso' (Spec (.of (Polynomial (ZMod p))))
          (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
          (torsionCoefficientReduce p ell (hkm.trans hmn))
          (torsionCoefficientReduce_comp p ell hkm hmn).symm).inv.app
            (kloostermanFiniteCoefficientDerivedImage p ell hne d k) := by
  let cS := (EtaleCoefficientRestriction.compIso' (Spec (.of (Polynomial (ZMod p))))
    (torsionCoefficientReduce p ell hmn) (torsionCoefficientReduce p ell hkm)
    (torsionCoefficientReduce p ell (hkm.trans hmn))
    (torsionCoefficientReduce_comp p ell hkm hmn).symm).app
      (kloostermanFiniteCoefficientDerivedImage p ell hne d k)
  have h : kloostermanFiniteCoefficientReduction p ell hne d hmn ≫
      (EtaleCoefficientRestriction.functor (Spec (.of (Polynomial (ZMod p))))
        (torsionCoefficientReduce p ell hmn)).map
          (kloostermanFiniteCoefficientReduction p ell hne d hkm) =
    kloostermanFiniteCoefficientReduction p ell hne d (hkm.trans hmn) ≫ cS.hom :=
    kloostermanFiniteCoefficientReduction_comp p ell hne d hkm hmn
  have h' := congrArg (fun z => z ≫ cS.inv) h
  simp only [assoc, Iso.hom_inv_id, comp_id] at h'
  exact h'.symm

#print axioms kloostermanFiniteCoefficientReduction_comp
#print axioms kloostermanFiniteCoefficientReduction_eq_comp_restrictScalars

end PrimeGap182.TypeIII
