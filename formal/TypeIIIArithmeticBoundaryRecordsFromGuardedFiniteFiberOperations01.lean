import TypeIIIArithmeticBoundaryInputsFromGuardedFiniteFiberOperations04

/-! Literal original Evaluation and Inputs for the computed guarded finite-fiber
BoundaryMaps. Independent standard local-stalk action and individual origin and
compact comparison Frobenius squares remain parameters; no native connecting
diagram, finished boundary record, or arithmetic model existence is supplied. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryRecordsFromGuardedFiniteFiberOperations
open PublishedPhysicalConstruction PublishedPhaseApplication PublishedMackey
open GeometricBoundaryFromFunctors ArithmeticBoundaryFromCanonicalLocalization
open ArithmeticDualFromCanonicalEvaluation ArithmeticBoundaryFromInvariantFunctors
open ArithmeticBoundaryFromGuardedFiniteFiberOperations RestrictionFrobenius
open ArithmeticBoundaryInputsFromGuardedFiniteFiberOperations

universe u v a b g t c d e
variable {Input : Type u} [Category.{v} Input] [MonoidalCategory Input]
  {Local : Type a} [Category.{b} Local] [MonoidalCategory Local]
  {G : Type g} [Group G] {Ginf : Type t} [Group Ginf]
  (along : Input ⥤ Local) [along.Monoidal]
  (J : Local ⥤ FDRep ℂ G) [J.Monoidal]
  {Point : Type c}
  {Native : Type} [Category.{d} Native]
  {Standard : Type} [Category.{e} Standard]
  (O : CurveDataFromOperations.Observables Input Point)
  (dual : Inputᵒᵖ ⥤ Input) (ev : ∀ A, dual.obj (op A) ⊗ A ⟶ 𝟙_ Input)
  (standardCurve : CurveData Input Point)
  (nativeH : CohomologyData Input Native) (nativeF : Native ⥤ ModuleCat.{0} ℂ)
  (standardH : CohomologyData Input Standard) (standardF : Standard ⥤ ModuleCat.{0} ℂ)
  (standardZero : Input ⥤ FDRep ℂ G)
  (zeroComparison : along ⋙ J ≅ standardZero)
  (infinity : Input ⥤ FDRep ℂ Ginf)
  (N : LocalizationData standardH standardF standardZero infinity)
  {p : ℕ} [Fact p.Prime] {h2 : 2 ≠ p}
  (R : LocalizationLaws standardCurve N p h2)
  (lisseMeaning : ∀ A, O.Lisse A → standardCurve.Lisse A)
  (slopeMeaning : ∀ A, (O.curveData dual).Isoclinic A 1 → standardCurve.Isoclinic A 1)
  (standardPositive : ∀ A, standardCurve.Isoclinic A 1 →
    Representation.invariants (infinity.obj A).ρ = ⊥)
  (bijective : ∀ A, O.Lisse A → Function.Bijective (canonicalDualMap (along ⋙ J) dual ev A))
  (compactComparison : ∀ A,
    nativeF.obj (nativeH.compact A) ≃ₗ[ℂ] standardF.obj (standardH.compact A))
  (ordinaryComparison : ∀ A, O.Lisse A → (O.curveData dual).TameZero A →
    (O.curveData dual).Isoclinic A 1 →
      nativeF.obj (nativeH.ordinary A) ≃ₗ[ℂ] standardF.obj (standardH.ordinary A))
  (supportSquare : ∀ A hL hT hS,
    (ordinaryComparison A hL hT hS).toLinearMap.comp (nativeF.map (nativeH.comparison A)).hom =
      (standardF.map (standardH.comparison A)).hom.comp (compactComparison A).toLinearMap)


/-- The computed canonical dual comparison satisfies the original evaluation role. -/
theorem arithmeticEvaluation : ArithmeticDualFromEvaluation.Comparison along dual ev O.Lisse
    (fun A hA => ((boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).dual A hA).toLinearEquiv) :=
  arithmeticComparison dual ev O.Lisse along J bijective

/-- The literal original arithmetic Inputs; connecting naturality is derived. -/
def boundaryInputs
    (P : ArithmeticRestriction ((boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))
    (nativeFr : nativeF ⟶ nativeF) (standardFr : standardF ⟶ standardF)
    (phi : G →* G)
    (nativeCov : ∀ A q x, (P.zeroFr (Z := ((boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) A (((along ⋙ J).obj A).ρ q x) =
      ((along ⋙ J).obj A).ρ (phi q) ((P.zeroFr (Z := ((boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) A x))
    (standardZeroFr : ∀ A, (standardZero.obj A).V ≃ₗ[ℂ] (standardZero.obj A).V)
    (standardCov : ∀ A q x, standardZeroFr A ((standardZero.obj A).ρ q x) =
      (standardZero.obj A).ρ (phi q) (standardZeroFr A x))
    (W : BoundaryWeilRecognition N standardFr standardZeroFr phi standardCov)
    (zeroFiberSquare : ∀ A x, (zeroComparison.app A).hom.hom.hom ((P.zeroFr (Z := ((boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) A x) =
      standardZeroFr A ((zeroComparison.app A).hom.hom.hom x))
    (compactFiberSquare : ∀ A x,
      compactComparison A ((nativeFr.app (nativeH.compact A)).hom x) =
        (standardFr.app (standardH.compact A)).hom (compactComparison A x)) :
    ArithmeticBoundaryFromInvariantFunctors.Inputs (boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).data
      (O.tensorComparison dual) (O.dualComparison dual) P nativeFr phi nativeCov where
  infinityFr := W.infinityFr
  infinityConjugation := W.infinityConjugation
  infinityCovariance := W.infinityCovariance
  connectingNatural A x y :=
    toCompact_natural along J nativeH nativeF standardH standardF standardZero zeroComparison
      infinity N compactComparison nativeFr standardFr (P.zeroFr (Z := ((boundaryMaps along J O dual ev standardCurve nativeH nativeF standardH standardF standardZero zeroComparison infinity N R lisseMeaning slopeMeaning standardPositive bijective compactComparison ordinaryComparison supportSquare).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) standardZeroFr phi nativeCov
        standardCov W zeroFiberSquare compactFiberSquare A x y

end PrimeGap182.TypeIII.ArithmeticBoundaryRecordsFromGuardedFiniteFiberOperations
