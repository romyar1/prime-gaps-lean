import TypeIIIArithmeticBoundaryFromGuardedFiniteFiberOperations04

/-! Reindex an independent standard localization diagram by source realization
and genuine group identifications. No new standard/native model is constructed,
and no native boundary or connecting compatibility is an input. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace PrimeGap182.TypeIII.ArithmeticBoundaryStandardLocalizationReindex
open PublishedPhysicalConstruction ArithmeticBoundaryFromCanonicalLocalization
open ArithmeticBoundaryFromInvariantFunctors
universe u v us vs p ps g gs t ts d
variable {Input : Type u} [Category.{v} Input]
  {StandardInput : Type us} [Category.{vs} StandardInput]
  {Point : Type p} {StandardPoint : Type ps}
  {G : Type g} [Group G] {StandardG : Type gs} [Group StandardG]
  {Gi : Type t} [Group Gi] {StandardGi : Type ts} [Group StandardGi]
  {C : Type} [Category.{d} C] [Abelian C]
  (source : Input ⥤ StandardInput)
  (origin : G ≃* StandardG) (infinity : Gi ≃* StandardGi)
  (H : CohomologyData StandardInput C) (F : C ⥤ ModuleCat.{0} ℂ)
  (zero : StandardInput ⥤ FDRep ℂ StandardG)
  (inf : StandardInput ⥤ FDRep ℂ StandardGi)

/-- Group restriction through an actual isomorphism preserves invariant vectors. -/
def invariantsChange (e : G ≃* StandardG) (V : FDRep ℂ StandardG) :
    Representation.invariants (FDRep.ρ ((Action.res (FGModuleCat ℂ) e.toMonoidHom).obj V)) ≃ₗ[ℂ]
      Representation.invariants V.ρ where
  toFun x := ⟨x.val, by
    intro q
    obtain ⟨r, rfl⟩ := e.surjective q
    exact x.property r⟩
  invFun x := ⟨x.val, fun q => x.property (e q)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Reindex compact/ordinary/support operations by one source realization. -/
def cohomology : CohomologyData Input C where
  compact A := H.compact (source.obj A)
  ordinary A := H.ordinary (source.obj A)
  comparison A := H.comparison (source.obj A)

/-- The tensor and dual slots are explicit caller operations. Only reindexed
Lisse/Isoclinic predicates are used by the localization theorem below. No
whole CurveRules or tensor/dual semantic realization is asserted here. -/
def curve (D : CurveData StandardInput StandardPoint)
    (tensor : Input → Input → Input) (dual : Input → Input)
    (point : Point → StandardPoint) : CurveData Input Point where
  tensor := tensor
  dual := dual
  Lisse A := D.Lisse (source.obj A)
  Pure A w := D.Pure (source.obj A) w
  rank A := D.rank (source.obj A)
  TameZero A := D.TameZero (source.obj A)
  BreaksLE A r := D.BreaksLE (source.obj A) r
  Isoclinic A r := D.Isoclinic (source.obj A) r
  swanZero A x := D.swanZero (source.obj A) (point x)
  swanInfinity A x := D.swanInfinity (source.obj A) (point x)

variable (N : LocalizationData H F zero inf)

/-- The standard operation arrows are reindexed, and only group labels change. -/
def localization : LocalizationData (cohomology source H) F
    ((source ⋙ zero) ⋙ Action.res (FGModuleCat ℂ) origin.toMonoidHom)
    ((source ⋙ inf) ⋙ Action.res (FGModuleCat ℂ) infinity.toMonoidHom) where
  boundaryObject A := N.boundaryObject (source.obj A)
  comparison A := N.comparison (source.obj A) ≪≫ₗ
    ((invariantsChange origin (zero.obj (source.obj A))).prodCongr
      (invariantsChange infinity (inf.obj (source.obj A)))).symm
  connecting A := N.connecting (source.obj A)
  globalSections A := N.globalSections (source.obj A)
  globalBoundary A := N.globalBoundary (source.obj A)
  projective A := N.projective (source.obj A)
  compactToProjective A := N.compactToProjective (source.obj A)
  leray A := N.leray (source.obj A)

variable (D : CurveData StandardInput StandardPoint)
  (tensor : Input → Input → Input) (dual : Input → Input) (point : Point → StandardPoint)
  {prime : ℕ} [Fact prime.Prime] {h2 : 2 ≠ prime}
  (R : LocalizationLaws D N prime h2)

include R in
omit [Abelian C] in
/-- ALL-object standard localization laws transfer with no native exactness premise. -/
theorem laws : LocalizationLaws (curve source D tensor dual point)
    (localization source origin infinity H F zero inf N) prime h2 where
  globalInfinityInjective A hL := by
    intro x y h
    apply R.globalInfinityInjective (source.obj A) hL
    apply Subtype.ext
    have hv := congrArg (fun z : Representation.invariants
      (FDRep.ρ (((source ⋙ inf) ⋙ Action.res (FGModuleCat ℂ) infinity.toMonoidHom).obj A)) => z.val) h
    exact hv
  boundaryExact A := R.boundaryExact (source.obj A)
  compactExact A := R.compactExact (source.obj A)
  lerayInjective A := R.lerayInjective (source.obj A)
  support A := R.support (source.obj A)

variable (Fr : F ⟶ F)
  (standardZeroFr : ∀ A, (zero.obj A).V ≃ₗ[ℂ] (zero.obj A).V)
  (standardPhi : StandardG →* StandardG)
  (standardCov : ∀ A q x, standardZeroFr A ((zero.obj A).ρ q x) =
    (zero.obj A).ρ (standardPhi q) (standardZeroFr A x))
  (W : BoundaryWeilRecognition N Fr standardZeroFr standardPhi standardCov)
  (nativePhi : G →* G)
  (changedCov : ∀ A q x, standardZeroFr (source.obj A)
      ((FDRep.ρ (((source ⋙ zero) ⋙ Action.res (FGModuleCat ℂ) origin.toMonoidHom).obj A)) q x) =
    (FDRep.ρ (((source ⋙ zero) ⋙ Action.res (FGModuleCat ℂ) origin.toMonoidHom).obj A)) (nativePhi q)
      (standardZeroFr (source.obj A) x))

/-- Standard closed-stalk arithmetic compatibility changes only group labels.
The new origin covariance is obtained from the full-Weil dictionary in the
actual application. No native connecting compatibility is provided here. -/
def weilRecognition : BoundaryWeilRecognition
    (localization source origin infinity H F zero inf N) Fr
    (fun A => standardZeroFr (source.obj A)) nativePhi changedCov where
  infinityFr A := W.infinityFr (source.obj A)
  infinityConjugation := infinity.symm.toMonoidHom.comp
    (W.infinityConjugation.comp infinity.toMonoidHom)
  infinityCovariance A q x := by
    change W.infinityFr (source.obj A) ((inf.obj (source.obj A)).ρ (infinity q) x) =
      (inf.obj (source.obj A)).ρ
        (infinity (infinity.symm (W.infinityConjugation (infinity q))))
        (W.infinityFr (source.obj A) x)
    simpa only [MulEquiv.apply_symm_apply] using
      W.infinityCovariance (source.obj A) (infinity q) x
  localStalkAction A x := by
    have hs := W.localStalkAction (source.obj A) x
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun pair => pair.1.val) hs
    · apply Subtype.ext
      exact congrArg (fun pair => pair.2.val) hs

end PrimeGap182.TypeIII.ArithmeticBoundaryStandardLocalizationReindex
