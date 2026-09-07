import TypeIIIDerivedBaseChange

/-!
# Compatibility of the derived comparison with degree zero

The comparison on cohomology is computed through the actual homology
factorization isomorphisms. Its degree-zero compatibility follows from
the augmentation equation for the original chain comparison.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

section Homology

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (H : D ⥤ D') [H.Additive] [H.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology comparison respects the actual quotient from cycles. -/
@[reassoc]
theorem exactFunctorHomologyIso_homologyπ (S : ShortComplex D) :
    (S.map H).homologyπ ≫ (S.mapHomologyIso H).hom =
      (S.mapCyclesIso H).hom ≫ H.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq H, S.leftHomologyData.mapCyclesIso_eq H]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  change (S.leftHomologyData.map H).cyclesIso.hom ≫
      H.map S.leftHomologyData.π ≫ H.map S.leftHomologyData.homologyIso.inv = _
  rw [← H.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, H.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison also respects the actual quotient from cycles. -/
@[reassoc]
theorem exactFunctorHomologyIso_inv_homologyπ (S : ShortComplex D) :
    H.map S.homologyπ ≫ (S.mapHomologyIso H).inv =
      (S.mapCyclesIso H).inv ≫ (S.map H).homologyπ := by
  rw [← cancel_mono (S.mapHomologyIso H).hom]
  simp [assoc, exactFunctorHomologyIso_homologyπ]

set_option backward.isDefEq.respectTransparency false in
/-- The actual homotopy-category comparison agrees with the original complex
comparison through the canonical factorization isomorphisms. -/
theorem exactFunctorHomotopyHomologyIso_inv_factors (K : CochainComplex D ℕ) (n : ℕ) :
    (exactFunctorHomotopyHomologyIso H (ComplexShape.up ℕ) n).inv.app
        ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj K) ≫
      (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.app
        ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) =
      H.map ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.app K) ≫
        (exactFunctorHomologyIso H (ComplexShape.up ℕ) n).inv.app K := by
  simp [exactFunctorHomotopyHomologyIso, Quotient.natIsoLift, Quotient.natTransLift,
    Functor.mapHomotopyCategoryFactors, HomotopyCategory.quotient_obj_as]

end Homology

section Derived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [HasInjectiveResolutions C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (F' : C' ⥤ D') [F'.Additive]
  (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : D ⥤ D') [H.Additive] [H.PreservesHomology]
  (β : F ⋙ H ⟶ G ⋙ F')

omit [HasInjectiveResolutions C] [H.PreservesHomology] in
set_option backward.isDefEq.respectTransparency false in
/-- The literal derived comparison chain map extends the original ordinary component. -/
theorem derivedBaseChangeChainMap_augmentation {A : C} (I : InjectiveResolution A) :
    H.map (F.map (I.ι.f 0)) ≫ (derivedBaseChangeChainMap F F' G H β I).f 0 =
      β.app A ≫ F'.map ((injectiveResolution (G.obj A)).ι.f 0) := by
  rw [derivedBaseChangeChainMap_f, ← assoc]
  erw [β.naturality]
  rw [assoc, Functor.comp_map, ← F'.map_comp]
  exact congrArg (fun k => β.app A ≫ F'.map k)
    (exactFunctorResolutionComparison_commutes G I)

omit [HasInjectiveResolutions C] in
set_option backward.isDefEq.respectTransparency false in
/-- On degree-zero cycles, the chain map gives the original component
after the canonical mapped-cycle comparison. -/
theorem derivedBaseChangeChainMap_cycles_zero {A : C} (I : InjectiveResolution A) :
    H.map (I.toRightDerivedZero' F) ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).mapCyclesIso H).inv ≫
      HomologicalComplex.cyclesMap (derivedBaseChangeChainMap F F' G H β I) 0 =
      β.app A ≫ (injectiveResolution (G.obj A)).toRightDerivedZero' F' := by
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L := (F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution (G.obj A)).cocomplex
  have hm : ((K.sc 0).mapCyclesIso H).inv ≫
      ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles 0 =
      H.map (K.iCycles 0) := by
    rw [← cancel_epi ((K.sc 0).mapCyclesIso H).hom]
    rw [Iso.hom_inv_id_assoc]
    change ((K.sc 0).map H).iCycles =
      ((K.sc 0).mapCyclesIso H).hom ≫ H.map (K.sc 0).iCycles
    exact (ShortComplex.mapCyclesIso_hom_iCycles (K.sc 0) H).symm
  apply (cancel_mono (L.iCycles 0)).mp
  dsimp only [K, L] at hm ⊢
  simp only [assoc, HomologicalComplex.cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  rw [← assoc ((K.sc 0).mapCyclesIso H).inv, hm, ← assoc, ← H.map_comp,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  exact derivedBaseChangeChainMap_augmentation F F' G H β I

omit [HasInjectiveResolutions C] in
set_option backward.isDefEq.respectTransparency false in
/-- Taking degree-zero homology of the literal chain map recovers the
original component on the augmentation classes. -/
theorem derivedBaseChangeChainMap_homology_zero {A : C} (I : InjectiveResolution A) :
    H.map (I.toRightDerivedZero' F ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 0) ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).mapHomologyIso H).inv ≫
      HomologicalComplex.homologyMap (derivedBaseChangeChainMap F F' G H β I) 0 =
      β.app A ≫ (injectiveResolution (G.obj A)).toRightDerivedZero' F' ≫
        ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (G.obj A)).cocomplex).homologyπ 0 := by
  rw [H.map_comp, assoc]
  erw [exactFunctorHomologyIso_inv_homologyπ_assoc]
  change H.map (I.toRightDerivedZero' F) ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).mapCyclesIso H).inv ≫
      ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homologyπ 0 ≫
      HomologicalComplex.homologyMap (derivedBaseChangeChainMap F F' G H β I) 0 = _
  rw [HomologicalComplex.homologyπ_naturality]
  simpa only [assoc] using congrArg (fun k => k ≫
    ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (G.obj A)).cocomplex).homologyπ 0)
    (derivedBaseChangeChainMap_cycles_zero F F' G H β I)

set_option backward.isDefEq.respectTransparency false in
/-- The derived map is the homology of its literal chain map, with the
canonical comparison for the exact coefficient-side functor. -/
theorem derivedBaseChangeMap_factors (n : ℕ) (A : C) :
    (derivedBaseChangeMap F F' G H β n).app A ≫
      (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.app
        ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (G.obj A)).cocomplex) =
      H.map ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution A).cocomplex)) ≫
      (exactFunctorHomologyIso H (ComplexShape.up ℕ) n).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution A).cocomplex) ≫
      (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
        (derivedBaseChangeChainMap F F' G H β (injectiveResolution A)) := by
  rw [derivedBaseChangeMap_app, derivedBaseChangeResolutionMap_app, assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).hom.naturality]
  rw [← assoc]
  erw [exactFunctorHomotopyHomologyIso_inv_factors H
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution A).cocomplex) n]
  rw [assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map to the zeroth derived functor is represented by
the actual augmentation class in the chosen resolution. -/
theorem toRightDerivedZero_factors (A : C) :
    F.toRightDerivedZero.app A ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) 0).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution A).cocomplex) =
      (injectiveResolution A).toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution A).cocomplex).homologyπ 0 := by
  change ((injectiveResolution A).toRightDerivedZero' F ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution A).cocomplex).homologyπ 0 ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) 0).inv.app _) ≫ _ = _
  simp
  erw [comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, the constructed derived comparison commutes with
the original ordinary transformation and the canonical derived maps. -/
theorem derivedBaseChangeMap_zero :
    Functor.whiskerRight F.toRightDerivedZero H ≫ derivedBaseChangeMap F F' G H β 0 =
      β ≫ Functor.whiskerLeft G F'.toRightDerivedZero := by
  ext A
  change H.map (F.toRightDerivedZero.app A) ≫ (derivedBaseChangeMap F F' G H β 0).app A =
    β.app A ≫ F'.toRightDerivedZero.app (G.obj A)
  apply (cancel_mono ((HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) 0).hom.app
    ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (G.obj A)).cocomplex))).mp
  rw [assoc, assoc, derivedBaseChangeMap_factors, ← H.map_comp_assoc,
    toRightDerivedZero_factors, toRightDerivedZero_factors]
  exact derivedBaseChangeChainMap_homology_zero F F' G H β (injectiveResolution A)

end Derived

#print axioms exactFunctorHomologyIso_homologyπ
#print axioms exactFunctorHomologyIso_inv_homologyπ
#print axioms exactFunctorHomotopyHomologyIso_inv_factors
#print axioms derivedBaseChangeChainMap_augmentation
#print axioms derivedBaseChangeChainMap_cycles_zero
#print axioms derivedBaseChangeChainMap_homology_zero
#print axioms derivedBaseChangeMap_factors
#print axioms toRightDerivedZero_factors
#print axioms derivedBaseChangeMap_zero

end PrimeGap182.TypeIII
