import TypeIIIPublishedLocalConstruction
import TypeIIITensorListRepresentation

/-!
# The canonical local perverse correlation and its infinity representation

Construct j_{0*}(Kl3 tensor (lambda^* Kl3)^dual)[1] from one source
object. Infinity restriction is a genuine strong monoidal functor. Its
general compatibility with duals and middle extension gives the infinity
identification required by the existing local Fourier theorem.

The scalar pullbacks below are the functors for the units x |-> c*x on
Gm over the generic direction field. Their geometric realization, the
ordinary middle-extension functor, and the general restriction laws are
explicit inputs. The zero entry of KloostermanInfinityData is unused and
is assigned the tensor unit, so no scalar-zero pullback on Gm is assumed.

The source Kloosterman infinity model remains the general published input
of Fu, Proposition 0.8 (https://arxiv.org/pdf/math/0702436v5). The finite
origin construction uses Laumon, section 2.3.2, through the existing module.
Neither a correlation infinity identification nor a Mackey comparison is
an assumption of the canonical endpoint. Its Fourier-stalk rank and its
identification with the global physical parabolic image remain unfinished.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalLocalCorrelation

open PublishedPhaseApplication PublishedMackey PublishedLocalConstruction
open TensorListRepresentation

universe u v w z t q a b c

variable {K : Type u} [Field K] {E : Type v} [Field E]
  {I : Type w} [Group I] {G : Type t} [Group G]
  {C : Type a} [Category.{b} C] [MonoidalCategory C]
  {Q : Type q} [Category.{c} Q]

/-- The operations on lisse sheaves on Gm. In the intended realization,
`scalar c` is pullback along the unit scaling x |-> c*x and
`middleExtension` is ordinary j_{0*} followed by the perverse shift [1]. -/
structure SheafOperations (L : Type u) [Field L] (C : Type a)
    [Category.{b} C] (Q : Type q) [Category.{c} Q] where
  scalar : Lˣ → C ⥤ C
  scalar_one : scalar 1 ≅ 𝟭 C
  dual : C → C
  middleExtension : C ⥤ Q

variable (O : SheafOperations (PhaseField K) C Q)
  (J : C ⥤ FDRep E I) [J.Monoidal]
  {F : LocalFourierData K E I G} (S : FiniteOriginData Q F)

/-- Restriction identities for every lisse object, with no selected
Kloosterman source, scalar parameter, or correlation in their statements. -/
structure InfinityCompatibility where
  dual : ∀ A, Representation.Equiv (J.obj (O.dual A)).ρ
    (dualRepresentation (J.obj A)).ρ
  middleExtension : ∀ A, Representation.Equiv
    (S.infinity (O.middleExtension.obj A)).ρ (J.obj A).ρ

/-- This is the literal lisse tensor recipe, before middle extension. -/
def correlation (kl : C) (lambda : (PhaseField K)ˣ) : C :=
  kl ⊗ O.dual ((O.scalar lambda).obj kl)

/-- The perverse object supplied to the existing finite-origin sequence. -/
def perverseCorrelation (kl : C) (lambda : (PhaseField K)ˣ) : Q :=
  O.middleExtension.obj (correlation O kl lambda)

/-- Infinity models of the same single source and its unit scalar
pullbacks. The zero branch is never used by the published model rule. -/
def sourceInfinity (kl : C) : KloostermanInfinityData (PhaseField K) E I where
  kl lambda := if h : lambda ≠ 0 then
      J.obj ((O.scalar (Units.mk0 lambda h)).obj kl)
    else J.obj (𝟙_ C)

omit [J.Monoidal] in
theorem sourceInfinity_unit (kl : C) (lambda : (PhaseField K)ˣ) :
    (sourceInfinity O J kl).kl lambda = J.obj ((O.scalar lambda).obj kl) := by
  simp only [sourceInfinity, dite_eq_left (Units.ne_zero lambda), Units.mk0_val]

/-- The identity scalar pullback gives the first source factor. -/
def sourceInfinityOneEquiv (kl : C) :
    Representation.Equiv (J.obj kl).ρ ((sourceInfinity O J kl).kl 1).ρ := by
  have h := sourceInfinity_unit O J kl 1
  exact (equivOfIso (J.mapIso ((O.scalar_one.app kl).symm))).trans
    (SelectedTensorTransport.representationEquivOfEq h.symm)

variable (R : InfinityCompatibility O J S)

/-- Derive the exact correlation infinity model by restricting the
constructed middle extension, tensor, and dual in that order. -/
def correlationInfinityEquiv (kl : C) (lambda : (PhaseField K)ˣ) :
    Representation.Equiv (S.infinity (perverseCorrelation O kl lambda)).ρ
      (tensor ((sourceInfinity O J kl).kl 1)
        (dualRepresentation ((sourceInfinity O J kl).kl lambda))).ρ :=
  (R.middleExtension (correlation O kl lambda)).trans
    ((equivOfIso (Functor.Monoidal.μIso J kl (O.dual ((O.scalar lambda).obj kl))).symm).trans
      ((monoidalTensorEquiv _ _).trans
        (tensorEquiv (sourceInfinityOneEquiv O J kl)
          ((R.dual ((O.scalar lambda).obj kl)).trans
            (dualEquiv (SelectedTensorTransport.representationEquivOfEq
              (sourceInfinity_unit O J kl lambda).symm))))))

/-- The actual nonzero generic angular parameter. -/
def angularUnit (m n : K) (hm : m ≠ 0) (hn : n ≠ 0) : (PhaseField K)ˣ :=
  Units.mk0 (angularRatio m n) (angularRatio_ne_zero m n hm hn)

/-- No supplied perverse object or supplied infinity comparison occurs
here: both are constructed from the same single source kl. -/
def angularInfinityEquiv (kl : C) (m n : K) (hm : m ≠ 0) (hn : n ≠ 0) :
    Representation.Equiv
      (S.infinity (perverseCorrelation O kl (angularUnit m n hm hn))).ρ
      (tensor ((sourceInfinity O J kl).kl 1)
        (dualRepresentation ((sourceInfinity O J kl).kl (angularRatio m n)))).ρ :=
  correlationInfinityEquiv O J S R kl (angularUnit m n hm hn)

variable [CharZero E] {H : Type z} [Group H]

/-- Apply the published finite-origin and cubic-cover laws to the
canonical object. The remaining rank assumption is stated explicitly. -/
def canonicalCoreLocalData (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (kl : C) (KR : KloostermanInfinityRules p P A (sourceInfinity O J kl))
    (FR : LocalFourierAdditivity F) (FA : CubicInputAdmissibility P A F)
    (SR : FiniteOriginRules p S) (hp : 3 < p)
    (alpha m n : K) (ha : alpha ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hrank : Module.finrank E
      (S.origin (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
        (perverseCorrelation O kl (angularUnit m n hm hn))) = 6) :
    CoreLocalData (cubicFourierData P A F FA) alpha m n
      (S.origin (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
        (perverseCorrelation O kl (angularUnit m n hm hn))) :=
  coreLocalDataOfPublished p P A (sourceInfinity O J kl) F PR AR KR FR FA S SR
    hp alpha m n ha hm hn (perverseCorrelation O kl (angularUnit m n hm hn))
    (angularInfinityEquiv O J S R kl m n hm hn) hrank

include R in
/-- The existing exhaustive local phase conclusion for the canonical
perverse correlation. The Fourier-stalk rank is still an explicit input. -/
theorem canonical_core_profile [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (kl : C) (KR : KloostermanInfinityRules p P A (sourceInfinity O J kl))
    (FR : LocalFourierAdditivity F) (FA : CubicInputAdmissibility P A F)
    (SR : FiniteOriginRules p S)
    (profile : PhaseData K E G) (phaseRules : PhaseRules profile)
    (fu : FuRules p profile (cubicFourierData P A F FA))
    (hp : 3 < p) (h2 : (2 : K) ≠ 0)
    (alpha m n : K) (ha : alpha ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hrank : Module.finrank E
      (S.origin (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
        (perverseCorrelation O kl (angularUnit m n hm hn))) = 6) :
    profile.HasProfile
        (S.origin (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
          (perverseCorrelation O kl (angularUnit m n hm hn))) ∧
      ∀ beta ∈ profile.phases
          (S.origin (radialScale alpha m) (radialScale_ne_zero alpha m ha hm)
            (perverseCorrelation O kl (angularUnit m n hm hn))),
        FuCubicSquaredPhase alpha m n beta :=
  core_profile_of_local_data phaseRules fu hp h2 alpha m n ha hm _
    (canonicalCoreLocalData O J S R p P A PR AR kl KR FR FA SR hp alpha m n ha hm hn hrank)

end PrimeGap182.TypeIII.CanonicalLocalCorrelation

#print axioms PrimeGap182.TypeIII.CanonicalLocalCorrelation.sourceInfinity_unit
#print axioms PrimeGap182.TypeIII.CanonicalLocalCorrelation.sourceInfinityOneEquiv
#print axioms PrimeGap182.TypeIII.CanonicalLocalCorrelation.correlationInfinityEquiv
#print axioms PrimeGap182.TypeIII.CanonicalLocalCorrelation.angularInfinityEquiv
#print axioms PrimeGap182.TypeIII.CanonicalLocalCorrelation.canonicalCoreLocalData
#print axioms PrimeGap182.TypeIII.CanonicalLocalCorrelation.canonical_core_profile
