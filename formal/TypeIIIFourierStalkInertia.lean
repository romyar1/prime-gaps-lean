import TypeIIIFourierStalkFromSources

/-!
# Inertia compatibility of the constructed Fourier-stalk comparison

The comparison uses the same linear equivalence already constructed from
localization and the three source specializations. General naturality of
cohomology, localization, and Fourier base change proves that it commutes
with inertia. No inertia comparison for the finished family is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.FourierStalkInertia

open PublishedPhysicalConstruction BoundaryFromSourceModels MiddleFromLocalization
open FourierStalkFromSources PublishedPhaseApplication PublishedLocalConstruction CanonicalLocalCorrelation

universe u v w z a b c d e f g i j h

/-- An inertia action on a cohomology functor, natural in every object
and morphism. This is independent of the selected correlation. -/
structure FunctorInertia {C : Type u} [Category.{v} C]
    (F : C ⥤ ModuleCat.{w} ℂ) (G : Type z) [Group G] where
  rho : ∀ X, Representation ℂ G (F.obj X)
  natural : ∀ {X Y} (f : X ⟶ Y) s,
    (F.map f).hom.comp (rho X s) = (rho Y s).comp (F.map f).hom

section General
variable {C : Type u} [Category.{v} C] {G : Type z} [Group G]
  {F : C ⥤ ModuleCat.{w} ℂ} (R : FunctorInertia F G)

/-- Every isomorphism of the source category gives an actual equivariant
linear equivalence under the same inertia functor. -/
def FunctorInertia.mapEquiv {X Y : C} (e : X ≅ Y) :
    Representation.Equiv (R.rho X) (R.rho Y) where
  toLinearEquiv := (F.mapIso e).toLinearEquiv
  isIntertwining' s := R.natural e.hom s

/-- The ordinary forgetful functor on the actual finite-dimensional
representation category. -/
def forgetInertia (G : Type z) [Group G] : FDRep ℂ G ⥤ ModuleCat ℂ :=
  forget₂ (FDRep ℂ G) (FGModuleCat ℂ) ⋙ forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)

/-- Construct these actions from an actual representation-valued functor,
rather than requiring independently chosen actions on its objects. -/
def FunctorInertia.ofFDRepFunctor (I : C ⥤ FDRep ℂ G) :
    FunctorInertia (I ⋙ forgetInertia G) G where
  rho X := (I.obj X).ρ
  natural f s := congrArg (fun f => f.hom.hom) ((I.map f).comm s)

end General

variable {K : Type u} [Field K]
  {Input : Type v} [Category.{c} Input] [MonoidalCategory Input]
  {Point : Type z} {C : Type w} [Category.{d} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{w} ℂ} {BS : BoundarySequence D H F}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F BS)
  (M : CompactificationData Z) (MR : CompactificationRules Z M)
  {G : Type c} [Group G]
  (RF : FunctorInertia F G) (RM : FunctorInertia M.affine G)

/-- Naturality of the compact-to-affine localization map, for every
curve input. No parabolic image or finished tensor appears in this law. -/
structure LocalizationInertia : Prop where
  compact_natural : ∀ A s,
    (M.fromCompact A).hom.comp (RF.rho (H.compact A) s) =
      (RM.rho A s).comp (M.fromCompact A).hom

variable (RI : LocalizationInertia Z M RF RM)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical image-to-affine comparison commutes with inertia.
Naturality of the original image quotient follows from the functor action. -/
def coreStalkAffineInertiaEquiv (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1) :
    Representation.Equiv (RF.rho (parabolicCore H A)) (RM.rho A) where
  toLinearEquiv := (coreStalkAffineIso Z M MR A hA hs).toLinearEquiv
  isIntertwining' s := by
    have h := coreStalkAffineIso_natural Z M MR A hA hs
      (ModuleCat.ofHom (RF.rho (H.compact A) s))
      (ModuleCat.ofHom (RF.rho (parabolicCore H A) s))
      (ModuleCat.ofHom (RM.rho A s))
      (by apply ModuleCat.hom_ext; exact RF.natural (Abelian.factorThruImage (H.comparison A)) s)
      (by apply ModuleCat.hom_ext; exact RI.compact_natural A s)
    exact congrArg (fun f => f.hom) h

variable {L : Type e} [Category.{f} L] [MonoidalCategory L]
  {Q : Type g} [Category.{i} Q]
  (O : SheafOperations (PhaseField K) L Q)
  (J : L ⥤ Input) [J.Monoidal] (dualInput : Inputᵒᵖ ⥤ Input)
  (T : SpecializationCompatibility (D := D) O J dualInput)
  {I : Type j} [Group I] {LF : LocalFourierData K ℂ I G}
  (FO : FiniteOriginData Q LF) (BC : FourierBaseChange Z M O J FO)

/-- General inertia naturality of compact Fourier base change on every
lisse object and every nonzero radial scale. -/
structure FourierInertia : Prop where
  natural : ∀ s hs A t,
    (BC.comparison s hs A).toLinearMap.comp ((FO.origin s hs (O.middleExtension.obj A)).ρ t) =
      (RM.rho (D.tensor (J.obj A) (BC.additive s hs)) t).comp
        (BC.comparison s hs A).toLinearMap

variable (BI : FourierInertia Z M RM O J FO BC)

/-- Lift general Fourier base change to an equivariant equivalence. -/
def fourierBaseChangeInertiaEquiv (s : PhaseField K) (hs : s ≠ 0) (A : L) :
    Representation.Equiv (FO.origin s hs (O.middleExtension.obj A)).ρ
      (RM.rho (D.tensor (J.obj A) (BC.additive s hs))) where
  toLinearEquiv := BC.comparison s hs A
  isIntertwining' t := BI.natural s hs A t

variable (A : KloostermanInputData D) (CR : CurveRules D)
  (kl : L) (lambda : (PhaseField K)ˣ) (s : PhaseField K) (hs : s ≠ 0)
  (hfirst : A.first ≅ J.obj kl)
  (hsecond : A.second ≅ J.obj ((O.scalar lambda).obj kl))
  (hadditive : A.additive ≅ BC.additive s hs)

/-- The actual original parabolic representation is the canonical
Fourier representation. The completed family's equivariance is derived. -/
def coreStalkFourierInertiaEquiv :
    Representation.Equiv (RF.rho (parabolicCore H A.input))
      (FO.origin s hs (perverseCorrelation O kl lambda)).ρ :=
  ((coreStalkAffineInertiaEquiv Z M MR RF RM RI A.input (A.input_lisse CR)
    (A.input_slope_one CR)).trans
    (RM.mapEquiv (inputKernelIso Z M O J dualInput T FO BC A kl lambda s hs
      hfirst hsecond hadditive))).trans
    (fourierBaseChangeInertiaEquiv Z M RM O J FO BC BI s hs
      (CanonicalLocalCorrelation.correlation O kl lambda)).symm

/-- The equivariant map is exactly the previously constructed linear
comparison, so its rank calculation and inertia action concern one map. -/
theorem coreStalkFourierInertiaEquiv_linear :
    (coreStalkFourierInertiaEquiv Z M MR RF RM RI O J dualInput T FO BC BI
      A CR kl lambda s hs hfirst hsecond hadditive).toLinearEquiv =
      coreStalkFourierEquiv Z M MR O J dualInput T FO BC A CR kl lambda s hs
        hfirst hsecond hadditive := rfl

end PrimeGap182.TypeIII.FourierStalkInertia

#print axioms PrimeGap182.TypeIII.FourierStalkInertia.FunctorInertia.mapEquiv
#print axioms PrimeGap182.TypeIII.FourierStalkInertia.FunctorInertia.ofFDRepFunctor
#print axioms PrimeGap182.TypeIII.FourierStalkInertia.coreStalkAffineInertiaEquiv
#print axioms PrimeGap182.TypeIII.FourierStalkInertia.fourierBaseChangeInertiaEquiv
#print axioms PrimeGap182.TypeIII.FourierStalkInertia.coreStalkFourierInertiaEquiv
#print axioms PrimeGap182.TypeIII.FourierStalkInertia.coreStalkFourierInertiaEquiv_linear
