import TypeIIIDerivedBaseChangeZero

/-!
# Composition of the original homology comparisons

The canonical cycle and homology comparisons for a composite of exact
additive functors equal the successive original comparisons.  The proof
uses the actual inclusion of cycles and quotient onto homology.  These
identities retain the comparisons already used by the derived
base-change map; no new choice of a comparison or coherence premise is
introduced.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D₁ : Type u₁} [Category.{v₁} D₁] [Abelian D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂] [Abelian D₂]
  {D₃ : Type u₃} [Category.{v₃} D₃] [Abelian D₃]
  (H : D₁ ⥤ D₂) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (H' : D₂ ⥤ D₃) [H'.Additive] [PreservesFiniteLimits H'] [PreservesFiniteColimits H']

set_option backward.isDefEq.respectTransparency false in
/-- The actual cycle comparison for the composite is the successive
cycle comparison, as detected by the original monomorphic cycle inclusion. -/
theorem exactFunctorMapCyclesIso_comp_hom (S : ShortComplex D₁) :
    (S.mapCyclesIso (H ⋙ H')).hom =
      ((S.map H).mapCyclesIso H').hom ≫ H'.map (S.mapCyclesIso H).hom := by
  apply (cancel_mono ((H ⋙ H').map S.iCycles)).mp
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  change ((S.map H).map H').iCycles =
    (((S.map H).mapCyclesIso H').hom ≫ H'.map (S.mapCyclesIso H).hom) ≫
      H'.map (H.map S.iCycles)
  rw [assoc, ← H'.map_comp, ShortComplex.mapCyclesIso_hom_iCycles,
    ShortComplex.mapCyclesIso_hom_iCycles]

set_option backward.isDefEq.respectTransparency false in
/-- The actual homology comparison for the composite is the successive
comparison, with equality proved on the original quotient from cycles. -/
theorem exactFunctorMapHomologyIso_comp_hom (S : ShortComplex D₁) :
    (S.mapHomologyIso (H ⋙ H')).hom =
      ((S.map H).mapHomologyIso H').hom ≫ H'.map (S.mapHomologyIso H).hom := by
  apply (cancel_epi (S.map (H ⋙ H')).homologyπ).mp
  rw [exactFunctorHomologyIso_homologyπ]
  change (S.mapCyclesIso (H ⋙ H')).hom ≫ H'.map (H.map S.homologyπ) =
    ((S.map H).map H').homologyπ ≫
      (((S.map H).mapHomologyIso H').hom ≫ H'.map (S.mapHomologyIso H).hom)
  rw [← assoc, exactFunctorHomologyIso_homologyπ]
  rw [assoc, ← H'.map_comp, exactFunctorHomologyIso_homologyπ, H'.map_comp,
    ← assoc, ← exactFunctorMapCyclesIso_comp_hom]

set_option backward.isDefEq.respectTransparency false in
/-- The same equality packages the original comparisons as isomorphisms. -/
theorem exactFunctorMapHomologyIso_comp (S : ShortComplex D₁) :
    S.mapHomologyIso (H ⋙ H') =
      (S.map H).mapHomologyIso H' ≪≫ H'.mapIso (S.mapHomologyIso H) := by
  apply Iso.ext
  exact exactFunctorMapHomologyIso_comp_hom H H' S

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison composes in the corresponding reverse order. -/
theorem exactFunctorMapHomologyIso_comp_inv (S : ShortComplex D₁) :
    (S.mapHomologyIso (H ⋙ H')).inv =
      H'.map (S.mapHomologyIso H).inv ≫ ((S.map H).mapHomologyIso H').inv := by
  rw [exactFunctorMapHomologyIso_comp, Iso.trans_inv, Functor.mapIso_inv]

set_option backward.isDefEq.respectTransparency false in
/-- The original comparison on actual complexes has the same
composition formula, in every degree and for every complex shape. -/
theorem exactFunctorHomologyIso_comp_app {ι : Type w} (c : ComplexShape ι) (n : ι)
    (K : HomologicalComplex D₁ c) :
    (exactFunctorHomologyIso (H ⋙ H') c n).app K =
      (exactFunctorHomologyIso H' c n).app ((H.mapHomologicalComplex c).obj K) ≪≫
        H'.mapIso ((exactFunctorHomologyIso H c n).app K) :=
  exactFunctorMapHomologyIso_comp H H' (K.sc n)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse component formula uses those same actual complex comparisons. -/
theorem exactFunctorHomologyIso_comp_inv_app {ι : Type w} (c : ComplexShape ι) (n : ι)
    (K : HomologicalComplex D₁ c) :
    (exactFunctorHomologyIso (H ⋙ H') c n).inv.app K =
      H'.map ((exactFunctorHomologyIso H c n).inv.app K) ≫
        (exactFunctorHomologyIso H' c n).inv.app ((H.mapHomologicalComplex c).obj K) :=
  exactFunctorMapHomologyIso_comp_inv H H' (K.sc n)

#print axioms exactFunctorMapCyclesIso_comp_hom
#print axioms exactFunctorMapHomologyIso_comp_hom
#print axioms exactFunctorMapHomologyIso_comp
#print axioms exactFunctorMapHomologyIso_comp_inv
#print axioms exactFunctorHomologyIso_comp_app
#print axioms exactFunctorHomologyIso_comp_inv_app

end PrimeGap182.TypeIII
