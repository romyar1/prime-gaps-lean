import TypeIIIArithmeticBoundaryFromGuardedFiniteFiberOperations04
import TypeIIIArithmeticBoundaryConnectingTransportRoot01

/-! Pure arithmetic transport for the computed guarded finite-fiber maps.
No actual trait/Weil interpretation or ordinary-support mate is constructed.
The only arithmetic comparison hypotheses concern individual coefficient and
compact-fiber operations. Standard connecting naturality follows from the
standard Frobenius natural transformation and its local boundary-stalk action.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryInputsFromGuardedFiniteFiberOperations
open PublishedPhysicalConstruction PublishedPhaseApplication PublishedMackey
open GeometricBoundaryFromFunctors ArithmeticBoundaryFromCanonicalLocalization
open ArithmeticDualFromCanonicalEvaluation ArithmeticBoundaryFromInvariantFunctors
open ArithmeticBoundaryFromGuardedFiniteFiberOperations RestrictionFrobenius

universe u v a b g t c d e

section InvariantComparison
variable {G : Type g} [Group G] {V W : FDRep ℂ G}
  (i : V ≅ W) (nativeFr : V.V ≃ₗ[ℂ] V.V) (standardFr : W.V ≃ₗ[ℂ] W.V)
  (phi : G →* G)
  (nativeCov : ∀ q x, nativeFr (V.ρ q x) = V.ρ (phi q) (nativeFr x))
  (standardCov : ∀ q x, standardFr (W.ρ q x) = W.ρ (phi q) (standardFr x))
  (fiberSquare : ∀ x, i.hom.hom.hom (nativeFr x) = standardFr (i.hom.hom.hom x))

-- The invariant-action square is derived from the individual acted-fiber square.
include fiberSquare in
theorem invariantAction_square (x : Representation.invariants V.ρ) :
    invariantAction W standardFr phi standardCov
      (((Rep.invariantsFunctor ℂ G).mapIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso i)).toLinearEquiv x) =
    ((Rep.invariantsFunctor ℂ G).mapIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso i)).toLinearEquiv
      (invariantAction V nativeFr phi nativeCov x) := by
  apply Subtype.ext
  exact (fiberSquare x.val).symm
end InvariantComparison

section Naturality
variable {Input : Type u} [Category.{v} Input]
  {Local : Type a} [Category.{b} Local]
  {G : Type g} [Group G] {Ginf : Type t} [Group Ginf]
  (along : Input ⥤ Local) (J : Local ⥤ FDRep ℂ G)
  {Native : Type} [Category.{d} Native]
  {Standard : Type} [Category.{e} Standard]
  (nativeH : CohomologyData Input Native) (nativeF : Native ⥤ ModuleCat.{0} ℂ)
  (standardH : CohomologyData Input Standard) (standardF : Standard ⥤ ModuleCat.{0} ℂ)
  (standardZero : Input ⥤ FDRep ℂ G) (zeroComparison : along ⋙ J ≅ standardZero)
  (infinity : Input ⥤ FDRep ℂ Ginf)
  (N : LocalizationData standardH standardF standardZero infinity)
  (compactComparison : ∀ A,
    nativeF.obj (nativeH.compact A) ≃ₗ[ℂ] standardF.obj (standardH.compact A))
  (nativeFr : nativeF ⟶ nativeF) (standardFr : standardF ⟶ standardF)
  (nativeZeroFr : ∀ A, ((along ⋙ J).obj A).V ≃ₗ[ℂ] ((along ⋙ J).obj A).V)
  (standardZeroFr : ∀ A, (standardZero.obj A).V ≃ₗ[ℂ] (standardZero.obj A).V)
  (phi : G →* G)
  (nativeCov : ∀ A q x, nativeZeroFr A (((along ⋙ J).obj A).ρ q x) =
    ((along ⋙ J).obj A).ρ (phi q) (nativeZeroFr A x))
  (standardCov : ∀ A q x, standardZeroFr A ((standardZero.obj A).ρ q x) =
    (standardZero.obj A).ρ (phi q) (standardZeroFr A x))
  (W : BoundaryWeilRecognition N standardFr standardZeroFr phi standardCov)
  (zeroFiberSquare : ∀ A x, (zeroComparison.app A).hom.hom.hom (nativeZeroFr A x) =
    standardZeroFr A ((zeroComparison.app A).hom.hom.hom x))
  (compactFiberSquare : ∀ A x,
    compactComparison A ((nativeFr.app (nativeH.compact A)).hom x) =
      (standardFr.app (standardH.compact A)).hom (compactComparison A x))

-- No native connecting diagram is supplied: it follows through the two comparisons.
include W zeroFiberSquare compactFiberSquare in
theorem toCompact_natural (A : Input)
    (x : Representation.invariants (((along ⋙ J).obj A).ρ))
    (y : Representation.invariants ((infinity.obj A).ρ)) :
    (nativeFr.app (nativeH.compact A)).hom
      (toCompact along J nativeH nativeF standardH standardF standardZero zeroComparison
        infinity N compactComparison A (x,y)) =
    toCompact along J nativeH nativeF standardH standardF standardZero zeroComparison
      infinity N compactComparison A
        (invariantAction ((along ⋙ J).obj A) (nativeZeroFr A) phi (nativeCov A) x,
         invariantAction (infinity.obj A) (W.infinityFr A) W.infinityConjugation
           (W.infinityCovariance A) y) := by
  let iB := (boundaryInvariantsComparison along J standardZero zeroComparison infinity A).toModuleIso
  let iC := (compactComparison A).toModuleIso
  let tauB := ModuleCat.ofHom ((invariantAction ((along ⋙ J).obj A)
      (nativeZeroFr A) phi (nativeCov A)).toLinearMap.prodMap
    (invariantAction (infinity.obj A) (W.infinityFr A) W.infinityConjugation
      (W.infinityCovariance A)).toLinearMap)
  let sigmaB := ModuleCat.ofHom ((invariantAction (standardZero.obj A)
      (standardZeroFr A) phi (standardCov A)).toLinearMap.prodMap
    (invariantAction (infinity.obj A) (W.infinityFr A) W.infinityConjugation
      (W.infinityCovariance A)).toLinearMap)
  let delta := ModuleCat.ofHom (connecting N A)
  have hB : tauB ≫ iB.hom = iB.hom ≫ sigmaB := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · exact (invariantAction_square (zeroComparison.app A) (nativeZeroFr A)
        (standardZeroFr A) phi (nativeCov A) (standardCov A) (zeroFiberSquare A) z.1).symm
    · rfl
  have hC : nativeFr.app (nativeH.compact A) ≫ iC.hom =
      iC.hom ≫ standardFr.app (standardH.compact A) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact compactFiberSquare A
  have hDelta : sigmaB ≫ delta = delta ≫ standardFr.app (standardH.compact A) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (connecting_natural N standardFr standardZeroFr phi standardCov W A z.1 z.2).symm
  exact (ArithmeticBoundaryConnectingTransportRoot01.frobenius_square_apply iB iC delta
    tauB (nativeFr.app (nativeH.compact A)) sigmaB (standardFr.app (standardH.compact A))
      hB hC hDelta (x,y)).symm
end Naturality

end PrimeGap182.TypeIII.ArithmeticBoundaryInputsFromGuardedFiniteFiberOperations
