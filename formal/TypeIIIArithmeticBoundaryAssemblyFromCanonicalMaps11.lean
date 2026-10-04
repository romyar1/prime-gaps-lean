import TypeIIIArithmeticBoundaryFromCanonicalLocalization03
import TypeIIIArithmeticDualFromCanonicalEvaluation02

/-! The three original arithmetic boundary roles are assembled from
the same canonical localization arrow and canonical evaluation pairing.
There is no chosen BoundaryMaps, dual evaluation equation, injection,
exactness, or connecting-Frobenius equation among the premises. Individual
general localization, local stalk, and finite-lisse dual theorems remain
explicit; this application does not construct a native adic realization. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryAssemblyFromCanonicalMaps
open PublishedPhysicalConstruction RestrictionFrobenius
open ArithmeticBoundaryFromCanonicalLocalization ArithmeticDualFromCanonicalEvaluation
universe u v a b g t c d
variable {Input : Type u} [Category.{v} Input] [MonoidalCategory Input]
  {Local : Type a} [Category.{b} Local] [MonoidalCategory Local]
  {G : Type g} [Group G] {Ginf : Type t} [Group Ginf]
  (along : Input ⥤ Local) [along.Monoidal]
  (J : Local ⥤ FDRep ℂ G) [J.Monoidal]
  {Point : Type c} {C : Type} [Category.{d} C] [Abelian C]
  (O : CurveDataFromOperations.Observables Input Point)
  (dual : Inputᵒᵖ ⥤ Input) (ev : ∀ A, dual.obj (op A) ⊗ A ⟶ 𝟙_ Input)
  {H : CohomologyData Input C} {F : C ⥤ ModuleCat.{0} ℂ}
  (infinity : Input ⥤ FDRep ℂ Ginf)
  (N : LocalizationData H F (along ⋙ J) infinity)
  {p : ℕ} [Fact p.Prime] {h2 : 2 ≠ p}
  (R : LocalizationLaws (O.curveData dual) N p h2)
  (positiveSlope : ∀ A, (O.curveData dual).Isoclinic A 1 → Representation.invariants (infinity.obj A).ρ = ⊥)
  (bijective : ∀ A, O.Lisse A → Function.Bijective (canonicalDualMap (along ⋙ J) dual ev A))

/-- The literal original map record; all selected mathematical fields
are computed by the two canonical-map applications. -/
def originalBoundaryMaps : ArithmeticZeroFromSpecialization.BoundaryMaps
    (Ginf := Ginf) (O.curveData dual) H F dual (along ⋙ J) :=
  boundaryMaps N R positiveSlope (dualComparison (along ⋙ J) dual ev O.Lisse bijective)

local notation "M" => originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective

omit [Abelian C] in
/-- The old evaluation role follows by definition, on exactly the computed dual. -/
theorem originalEvaluation : ArithmeticDualFromEvaluation.Comparison along dual ev O.Lisse
    (fun A hA => ((M).dual A hA).toLinearEquiv) :=
  arithmeticComparison dual ev O.Lisse along J bijective

/-- Naturality of the canonical localization arrow fills the original
arithmetic boundary role. The restriction and covariance are explicit
parameters so their identities cannot be erased by section elaboration. -/
def originalBoundaryInputs
    (P : ArithmeticRestriction ((originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective).data.restriction (O.tensorComparison dual) (O.dualComparison dual))) (Fr : F ⟶ F) (phi : G →* G)
    (cov : ∀ A g x, (P.zeroFr (Z := ((originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) A (((along ⋙ J).obj A).ρ g x) =
      ((along ⋙ J).obj A).ρ (phi g) ((P.zeroFr (Z := ((originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) A x))
    (W : BoundaryWeilRecognition N Fr (P.zeroFr (Z := ((originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) phi cov) :
    ArithmeticBoundaryFromInvariantFunctors.Inputs (originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective).data
      (O.tensorComparison dual) (O.dualComparison dual) P Fr phi cov where
  infinityFr := W.infinityFr
  infinityConjugation := W.infinityConjugation
  infinityCovariance := W.infinityCovariance
  connectingNatural A x y := by
    exact connecting_natural (G0 := G) (Ginf := Ginf) (zero := along ⋙ J)
      (infinity := infinity) N Fr (P.zeroFr (Z := ((originalBoundaryMaps along J O dual ev infinity N R positiveSlope bijective).data.restriction (O.tensorComparison dual) (O.dualComparison dual)))) phi cov W A x y

end PrimeGap182.TypeIII.ArithmeticBoundaryAssemblyFromCanonicalMaps
