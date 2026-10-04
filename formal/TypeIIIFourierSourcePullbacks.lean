import TypeIIIFourierSourceMaps

/-!
# Source isomorphisms from the actual Fourier maps

The scalar operation and all three source comparisons are constructed
from inverse-image functors and general composition laws. The same Kl3
object on A1_K is restricted to the local x-line; the same AS object is
pulled back by the normalized additive map. No completed source
specialization is an input to these constructions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.FourierSourcePullbacks

open StartingSourceMaps GenericSourceSpecialization FourierSourceMaps PublishedPhaseApplication

universe u v w z a b c d e f g
variable (K : Type u) [Field K]
  {Line : Type v} [Category.{a} Line] {Input : Type w} [Category.{b} Input]
  {GenericInput : Type z} [Category.{c} GenericInput] {L : Type d} [Category.{e} L]
  (P : GenericSourceSpecialization.PullbackComposition
    (Line := Line) (Input := Input) (GenericInput := GenericInput) K)

/-- The local and generic inverse images, with their general composition
isomorphisms. Every source map and local scalar map is quantified. -/
structure LocalPullbacks where
  restriction : (localScheme K ⟶ affineLine K) → Line ⥤ L
  fromLocal : (genericScheme K ⟶ localScheme K) → L ⥤ GenericInput
  localEnd : (localScheme K ⟶ localScheme K) → L ⥤ L
  localEnd_id : localEnd (𝟙 (localScheme K)) ≅ 𝟭 L
  localComposition : ∀ g f, restriction f ⋙ fromLocal g ≅ P.generic (g ≫ f)
  localEndComposition : ∀ g h, localEnd h ⋙ fromLocal g ≅ fromLocal (g ≫ h)

variable (R : LocalPullbacks (L := L) K P)

def localSpecialization : L ⥤ GenericInput := R.fromLocal (projectionMorphism K)

def localSource (kl : Line) : L := (R.restriction (localInputMorphism K)).obj kl

def additiveSource (as : Line) (s : (PhaseField K)ˣ) : GenericInput :=
  (P.generic (additiveMorphism K s)).obj as

/-- The original canonical source construction uses these very same
inverse-image functors on the three original scheme maps. -/
def originalPullbackData : StartingSourceComplexity.PullbackData K Line Input where
  pullback f A := (P.original f).obj A

variable {Q : Type f} [Category.{g} Q]

/-- Construct the local scalar operation from the actual scheme map.
Its identity law follows from scalarMorphism_one and identity pullback. -/
def localSheafOperations (dual : L → L) (middle : L ⥤ Q) :
    CanonicalLocalCorrelation.SheafOperations (PhaseField K) L Q where
  scalar lambda := R.localEnd (scalarMorphism K lambda)
  scalar_one := eqToIso (congrArg R.localEnd (scalarMorphism_one K)) ≪≫ R.localEnd_id
  dual := dual
  middleExtension := middle

variable (alpha m n : Kˣ)

def firstSourceIso (kl : Line) :
    (P.along (specializationMorphism K alpha m n)).obj ((P.original (inputMorphism K 0)).obj kl) ≅
      (localSpecialization K P R).obj (localSource K P R kl) :=
  (sourcePullbackIso K alpha m n P 0).app kl ≪≫
    eqToIso (congrArg (fun f => (P.generic f).obj kl) (first_inputMorphism K alpha m n).symm) ≪≫
    ((R.localComposition (projectionMorphism K) (localInputMorphism K)).app kl).symm

def secondSourceIso (kl : Line) :
    (P.along (specializationMorphism K alpha m n)).obj ((P.original (inputMorphism K 1)).obj kl) ≅
      (localSpecialization K P R).obj
        ((R.localEnd (scalarMorphism K (lambdaUnit K m n))).obj (localSource K P R kl)) :=
  (sourcePullbackIso K alpha m n P 1).app kl ≪≫
    eqToIso (congrArg (fun f => (P.generic f).obj kl) (second_inputMorphism K alpha m n).symm) ≪≫
    ((R.localComposition (projectionMorphism K ≫ scalarMorphism K (lambdaUnit K m n))
      (localInputMorphism K)).app kl).symm ≪≫
    ((R.localEndComposition (projectionMorphism K) (scalarMorphism K (lambdaUnit K m n))).app
      (localSource K P R kl)).symm

def additiveSourceIso (as : Line) :
    (P.along (specializationMorphism K alpha m n)).obj ((P.original (inputMorphism K 2)).obj as) ≅
      additiveSource K P as (scaleUnit K alpha m) :=
  (sourcePullbackIso K alpha m n P 2).app as ≪≫
    eqToIso (congrArg (fun f => (P.generic f).obj as) (additive_inputMorphism K alpha m n).symm)

end PrimeGap182.TypeIII.FourierSourcePullbacks

#print axioms PrimeGap182.TypeIII.FourierSourcePullbacks.localSheafOperations
#print axioms PrimeGap182.TypeIII.FourierSourcePullbacks.firstSourceIso
#print axioms PrimeGap182.TypeIII.FourierSourcePullbacks.secondSourceIso
#print axioms PrimeGap182.TypeIII.FourierSourcePullbacks.additiveSourceIso
