import TypeIIIArithmeticBoundaryFromInvariantFunctors
import TypeIIIArithmeticZeroFromSpecialization

/-! Canonical ordinary boundary injection and arithmetic compatibility.
All connecting maps are images of native localization morphisms. The
GENERAL localization/Leray and local boundary-stalk/Weil recognitions
remain explicit; no BoundaryMaps/Inputs or connecting-natural provider
is an assumption. No adic foundation is reconstructed. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryFromCanonicalLocalization
open PublishedPhysicalConstruction PublishedPhaseApplication PublishedMackey
open ArithmeticZeroFromSpecialization GeometricBoundaryFromFunctors
open ArithmeticBoundaryFromInvariantFunctors RestrictionFrobenius
universe u v a b c d
variable {Input : Type u} [Category.{c} Input]
  {Point : Type v} {C : Type} [Category.{d} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat.{0} ℂ) (dualInput : Inputᵒᵖ ⥤ Input)
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (zero : Input ⥤ FDRep ℂ G0) (infinity : Input ⥤ FDRep ℂ Ginf)

/-- Independent native boundary object and actual ordinary localization
arrows. No injectivity, exactness or arithmetic equation is a field. -/
structure LocalizationData where
  boundaryObject : Input → C
  comparison : ∀ A, F.obj (boundaryObject A) ≃ₗ[ℂ]
    (Representation.invariants (zero.obj A).ρ × Representation.invariants (infinity.obj A).ρ)
  connecting : ∀ A, boundaryObject A ⟶ H.compact A
  globalSections : Input → ModuleCat.{0} ℂ
  globalBoundary : ∀ A, globalSections A →ₗ[ℂ] F.obj (boundaryObject A)
  projective : Input → ModuleCat.{0} ℂ
  compactToProjective : ∀ A, F.obj (H.compact A) →ₗ[ℂ] projective A
  leray : ∀ A, projective A →ₗ[ℂ] F.obj (H.ordinary A)

variable {H F zero infinity} (N : LocalizationData H F zero infinity)

/-- The connecting map is computed through the actual native morphism. -/
def connecting (A : Input) :
    (Representation.invariants (zero.obj A).ρ × Representation.invariants (infinity.obj A).ρ) →ₗ[ℂ] F.obj (H.compact A) :=
  (F.map (N.connecting A)).hom.comp (N.comparison A).symm.toLinearMap

def globalInfinity (A : Input) : N.globalSections A →ₗ[ℂ] Representation.invariants (infinity.obj A).ρ :=
  (LinearMap.snd ℂ _ _).comp ((N.comparison A).toLinearMap.comp (N.globalBoundary A))

/-- Individual GENERAL full-P1 ordinary localization and Leray laws on
ALL ordinary objects. Only connected-lisse evaluation needs lissity.
The characteristic parameters record the intended continuous 2-adic scope. -/
structure LocalizationLaws (p : ℕ) [Fact p.Prime] (_h2 : 2 ≠ p) : Prop where
  globalInfinityInjective : ∀ A, D.Lisse A → Function.Injective (globalInfinity N A)
  boundaryExact : ∀ A, LinearMap.range (N.globalBoundary A) = LinearMap.ker (F.map (N.connecting A)).hom
  compactExact : ∀ A, LinearMap.range (F.map (N.connecting A)).hom = LinearMap.ker (N.compactToProjective A)
  lerayInjective : ∀ A, Function.Injective (N.leray A)
  support : ∀ A, (N.leray A).comp (N.compactToProjective A) = (F.map (H.comparison A)).hom

variable {D dualInput} {p : ℕ} [Fact p.Prime] {h2 : 2 ≠ p}
  (R : LocalizationLaws D N p h2)
  (positiveSlope : ∀ A, D.Isoclinic A 1 → Representation.invariants (infinity.obj A).ρ = ⊥)

include R positiveSlope in
omit [Abelian C] in
theorem globalSections_zero (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1) (x : N.globalSections A) : x = 0 := by
  apply R.globalInfinityInjective A hA
  rw [map_zero]
  apply Subtype.ext
  have hx := (globalInfinity N A x).property
  have hz := (le_of_eq (positiveSlope A hs)) hx
  simpa using hz

include R positiveSlope in
omit [Abelian C] in
theorem connecting_injective (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1) : Function.Injective (connecting N A) := by
  have hg : N.globalBoundary A = 0 := by
    apply LinearMap.ext
    intro x
    rw [globalSections_zero N R positiveSlope A hA hs x]
    simp
  have hi : Function.Injective (F.map (N.connecting A)).hom := by
    apply LinearMap.ker_eq_bot.mp
    rw [← R.boundaryExact A, hg, LinearMap.range_zero]
  exact hi.comp (N.comparison A).symm.injective

include R in
omit [Abelian C] in
theorem connecting_exact (A : Input) : LinearMap.range (connecting N A) = LinearMap.ker (F.map (H.comparison A)).hom := by
  have hr : LinearMap.range (connecting N A) = LinearMap.range (F.map (N.connecting A)).hom := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨(N.comparison A).symm x,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨N.comparison A x,by simp [connecting]⟩
  rw [hr, R.compactExact A, ← R.support A]
  ext x
  change N.compactToProjective A x = 0 ↔ N.leray A (N.compactToProjective A x) = 0
  constructor
  · intro hx
    rw [hx,map_zero]
  · intro hx
    apply R.lerayInjective A
    simpa using hx

variable (dualComparison : ∀ A, D.Lisse A → Representation.Equiv
  (zero.obj (dualInput.obj (op A))).ρ (dualRepresentation (zero.obj A)).ρ)

/-- Literal original arithmetic BoundaryMaps with injection/exactness
computed from general laws and the same native connecting morphism. -/
def boundaryMaps : BoundaryMaps (Ginf := Ginf) D H F dualInput zero where
  infinity := infinity
  dual := dualComparison
  positiveSlope := positiveSlope
  toCompact := connecting N
  injective := connecting_injective N R positiveSlope
  exact := fun A _ _ _ => connecting_exact N R A

variable {R positiveSlope dualComparison}
  (Fr : F ⟶ F) (zeroFr : ∀ A, (zero.obj A).V ≃ₗ[ℂ] (zero.obj A).V)
  (phi : G0 →* G0)
  (cov : ∀ A g x, zeroFr A ((zero.obj A).ρ g x) = (zero.obj A).ρ (phi g) (zeroFr A x))

/-- Independent local boundary-stalk/Weil identification, ALL ordinary
objects. It contains no connecting arrow or compact-cohomology diagram.
Its intended general realization is the actual closed-boundary stalk
sum with the SAME local geometric Weil lifts. -/
structure BoundaryWeilRecognition where
  infinityFr : ∀ A, (infinity.obj A).V ≃ₗ[ℂ] (infinity.obj A).V
  infinityConjugation : Ginf →* Ginf
  infinityCovariance : ∀ A g x, infinityFr A ((infinity.obj A).ρ g x) =
    (infinity.obj A).ρ (infinityConjugation g) (infinityFr A x)
  localStalkAction : ∀ A x,
    N.comparison A ((Fr.app (N.boundaryObject A)).hom x) =
      (invariantAction (zero.obj A) (zeroFr A) phi (cov A) (N.comparison A x).1,
       invariantAction (infinity.obj A) (infinityFr A) infinityConjugation (infinityCovariance A) (N.comparison A x).2)

variable (W : BoundaryWeilRecognition N Fr zeroFr phi cov)
include W in
omit [Abelian C] in
theorem connecting_natural (A : Input) (x : Representation.invariants (zero.obj A).ρ) (y : Representation.invariants (infinity.obj A).ρ) :
    (Fr.app (H.compact A)).hom (connecting N A (x,y)) = connecting N A
      (invariantAction (zero.obj A) (zeroFr A) phi (cov A) x,
       invariantAction (infinity.obj A) (W.infinityFr A) W.infinityConjugation (W.infinityCovariance A) y) := by
  let z := (N.comparison A).symm (x,y)
  have hn := congrArg (fun f : F.obj (N.boundaryObject A) ⟶ F.obj (H.compact A) => f.hom z) (Fr.naturality (N.connecting A))
  change (Fr.app (H.compact A)).hom ((F.map (N.connecting A)).hom z) =
    (F.map (N.connecting A)).hom ((Fr.app (N.boundaryObject A)).hom z) at hn
  have hz : (Fr.app (N.boundaryObject A)).hom z = (N.comparison A).symm
      (invariantAction (zero.obj A) (zeroFr A) phi (cov A) x,
       invariantAction (infinity.obj A) (W.infinityFr A) W.infinityConjugation (W.infinityCovariance A) y) := by
    apply (N.comparison A).injective
    rw [W.localStalkAction]
    simp [z]
  change (Fr.app (H.compact A)).hom ((F.map (N.connecting A)).hom z) = _
  rw [hn,hz]
  rfl
end PrimeGap182.TypeIII.ArithmeticBoundaryFromCanonicalLocalization
