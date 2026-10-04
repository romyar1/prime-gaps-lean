import TypeIIIFiniteRepresentationCoefficientMonoidal
import TypeIIIPrimitiveRamificationFromGeneralKatzTheory
import TypeIIIPowerCoverBaseChangeFromEtaleCartesian

/-!
The base and covering infinity functors are computed from the SAME ordinary
two-adic geometric infinity realization and the fixed coefficient equivalence.
The covering group is the image of the actual supplied power-cover embedding;
its source identification is computed from injectivity. Neither a separate
cover nearby functor nor a selected cubic representation is supplied.
Interpreting the universal power embeddings as geometric inertia remains
external model data. This pure transport does not prove the nearby/push theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding
namespace PrimeGap182.TypeIII.InfinityNearbyFromComputedPowerEmbedding
open PrimitiveRamificationFromGeneralKatzTheory FiniteRepresentationCoefficientTransport
open PowerCoverBaseChangeFromEtaleCartesian

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (M : LocalRealization C)

def coefficientInfinityFunctor (E : Type) [Field E] :
    FDRep (PadicAlgCl 2) (M.infinityGroup E) ⥤ FDRep ℂ (M.infinityGroup E) :=
  (coefficientEquivalence TwoAdicComplexEmbedding.complexEquiv (M.infinityGroup E)).functor

def nearbyInfinity (E : Type) [Field E] :
    C (ArithmeticSourceMaps.fiberScheme E) ⥤ FDRep ℂ (M.infinityGroup E) :=
  M.infinity E ⋙ coefficientInfinityFunctor C M E

variable
  (powerEmbedding : ∀ (E : Type) [Field E] (_n : ℕ), M.infinityGroup E →* M.infinityGroup E)
  (powerInjective : ∀ (E : Type) [Field E] (n : ℕ), powerCoverGuard E n → Function.Injective (powerEmbedding E n))

def powerSubgroup (E : Type) [Field E] (n : ℕ) : Subgroup (M.infinityGroup E) :=
  (powerEmbedding E n).range

def powerSourceEquiv (E : Type) [Field E] (n : ℕ) (hn : powerCoverGuard E n) :
    M.infinityGroup E ≃* powerSubgroup C M powerEmbedding E n :=
  MonoidHom.ofInjective (powerInjective E n hn)

omit [∀ X, Abelian (C X)] in
theorem powerSourceEquiv_subtype (E : Type) [Field E] (n : ℕ) (hn : powerCoverGuard E n) :
    (powerSubgroup C M powerEmbedding E n).subtype.comp
      (powerSourceEquiv C M powerEmbedding powerInjective E n hn).toMonoidHom =
    powerEmbedding E n := by
  ext g
  rfl

def coefficientCoverFunctor (E : Type) [Field E] (n : ℕ) :
    FDRep (PadicAlgCl 2) (powerSubgroup C M powerEmbedding E n) ⥤
      FDRep ℂ (powerSubgroup C M powerEmbedding E n) :=
  (coefficientEquivalence TwoAdicComplexEmbedding.complexEquiv
    (powerSubgroup C M powerEmbedding E n)).functor

def coverNearbyPadic (E : Type) [Field E] (n : ℕ) (hn : powerCoverGuard E n) :
    C (ArithmeticSourceMaps.fiberScheme E) ⥤
      FDRep (PadicAlgCl 2) (powerSubgroup C M powerEmbedding E n) :=
  M.infinity E ⋙ Action.res (FGModuleCat (PadicAlgCl 2))
    (powerSourceEquiv C M powerEmbedding powerInjective E n hn).symm.toMonoidHom

def coverNearby (E : Type) [Field E] (n : ℕ) (hn : powerCoverGuard E n) :
    C (ArithmeticSourceMaps.fiberScheme E) ⥤
      FDRep ℂ (powerSubgroup C M powerEmbedding E n) :=
  coverNearbyPadic C M powerEmbedding powerInjective E n hn ⋙
    coefficientCoverFunctor C M powerEmbedding E n

def coverCoefficientRestrictionIso (E : Type) [Field E] (n : ℕ) (hn : powerCoverGuard E n) :
    coverNearby C M powerEmbedding powerInjective E n hn ≅
      nearbyInfinity C M E ⋙ Action.res (FGModuleCat ℂ)
        (powerSourceEquiv C M powerEmbedding powerInjective E n hn).symm.toMonoidHom :=
  Functor.isoWhiskerLeft (M.infinity E)
    (restrictionIso TwoAdicComplexEmbedding.complexEquiv (M.infinityGroup E)
      (powerSourceEquiv C M powerEmbedding powerInjective E n hn).symm.toMonoidHom)

omit [∀ X, Abelian (C X)] in
theorem coverNearby_finrank (E : Type) [Field E] (n : ℕ) (hn : powerCoverGuard E n) (A : C (ArithmeticSourceMaps.fiberScheme E)) :
    Module.finrank ℂ ((coverNearby C M powerEmbedding powerInjective E n hn).obj A) =
      Module.finrank (PadicAlgCl 2) ((M.infinity E).obj A) :=
  finrank_eq TwoAdicComplexEmbedding.complexEquiv (powerSubgroup C M powerEmbedding E n)
    ((coverNearbyPadic C M powerEmbedding powerInjective E n hn).obj A)

end PrimeGap182.TypeIII.InfinityNearbyFromComputedPowerEmbedding
