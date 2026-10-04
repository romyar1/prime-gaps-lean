import TypeIIISourceInverseImageSystem
import TypeIIIPrimitiveRadialAS

/-!
# Radial pole characters on the physical parameter stalk

The local curve and parameter curve are copies of the same punctured
line. Pullback along the coordinate-preserving identity, followed by the
existing parameter inertia functor, supplies radial inertia on the local
category. The compositor identifies every pole character with the direct
parameter pullback of the original AS source, including coefficient zero.

General character laws and quadratic-cover base change remain published
inputs on these direct parameter stalks. Their transport to the existing
Fu application is proved below; no independent radial inertia functor is
supplied. This does not identify radial inertia with infinity inertia.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.PrimitiveRadialFromParameter

open SourceInverseImageSystem FourierSourceMaps GenericCurvePullback
open StartingSourceMaps PublishedPhaseApplication PrimitiveRadialAS
open FuFromQuadraticPullback TensorListRepresentation PublishedMackey

universe v w e g t
variable {K : Type} [Field K] (B : System.{v,w} K)
  {E : Type e} [Field E] {G : Type g} [Group G]
  (J : B.Obj .parameter ⥤ FDRep E G)

/-- Use the same coordinate at the radial origin on both copies of Gm. -/
def radialInertia : B.Obj .localCurve ⥤ FDRep E G :=
  B.pull (X := .parameter) (Y := .localCurve) (𝟙 (localScheme K)) ⋙ J

/-- Direct pole pullbacks to the parameter curve, before taking its stalk. -/
def parameterRestriction (f : localScheme K ⟶ affineLine K) :
    B.Obj .line ⥤ B.Obj .parameter :=
  B.pull (X := .parameter) (Y := .line) f

/-- The actual inverse-image compositor, evaluated at the same AS object. -/
def phaseEquiv (as : B.Obj .line) (beta : PhaseField K) :
    Representation.Equiv
      (phase K B.localPullbacks.restriction (radialInertia B J) as beta).ρ
      (phase K (parameterRestriction B) J as beta).ρ := by
  have h := B.composition (X := .parameter) (Y := .localCurve)
    (Z := .line) (𝟙 (localScheme K)) (poleMorphism K beta)
  rw [Category.id_comp (poleMorphism K beta)] at h
  exact equivOfIso (J.mapIso (h.app as))

variable [CharZero E] (D : PhaseData K E G) (R : PhaseRules D) (as : B.Obj .line)

include R in
/-- Profile, rank and the exact coefficient set are transported together. -/
theorem localPhaseLaws (laws : PhaseLaws K D (parameterRestriction B) J as) :
    PhaseLaws K D B.localPullbacks.restriction (radialInertia B J) as where
  profile beta :=
    (R.transport _ _ (phaseEquiv B J as beta).toIntertwiningMap
      (phaseEquiv B J as beta).toLinearEquiv.bijective).1.mpr (laws.profile beta)
  rank beta := (phaseEquiv B J as beta).toLinearEquiv.finrank_eq.trans (laws.rank beta)
  phases beta :=
    (R.transport _ _ (phaseEquiv B J as beta).toIntertwiningMap
      (phaseEquiv B J as beta).toLinearEquiv.bijective).2.trans (laws.phases beta)

/-- The general published inputs use the already selected parameter stalk.
There is no independently selectable inertia realization in this record. -/
structure Inputs (p : ℕ) [Fact p.Prime] [CharP K p]
    (C : CubicFourierData K E G) where
  laws : PhaseLaws K D (parameterRestriction B) J as
  Twist : Type t
  quadratic : QuadraticData (K := K) (E := E) (G := G) Twist
  coverRules : QuadraticRules p (models K D (parameterRestriction B) J as laws) quadratic
  comparison : FuComparison p C quadratic

variable (p : ℕ) [Fact p.Prime] [CharP K p]
  {C : CubicFourierData K E G}

/-- Preserve both quadratic branches and their maps under the compositor. -/
def Inputs.localCoverRules (S : Inputs B J D as p C) :
    QuadraticRules p
      (models K D B.localPullbacks.restriction (radialInertia B J) as
        (localPhaseLaws B J D R as S.laws)) S.quadratic where
  split hp A c b theta twist hA hc ht :=
    (S.coverRules.split hp A c b theta twist hA hc ht).trans
      (finiteSumEquiv (fun i : Fin 2 =>
        (phaseEquiv B J as (signedCoefficient b theta i)).symm))

/-- Supply the existing Fu application with the shared parameter realization. -/
def Inputs.toPrimitiveInputs (S : Inputs B J D as p C) :
    PrimitiveRadialAS.Inputs K p D C B.localPullbacks.restriction as where
  inertia := radialInertia B J
  laws := localPhaseLaws B J D R as S.laws
  Twist := S.Twist
  quadratic := S.quadratic
  coverRules := S.localCoverRules B J D R as p
  comparison := S.comparison

end PrimeGap182.TypeIII.PrimitiveRadialFromParameter

#print axioms PrimeGap182.TypeIII.PrimitiveRadialFromParameter.phaseEquiv
#print axioms PrimeGap182.TypeIII.PrimitiveRadialFromParameter.localPhaseLaws
#print axioms PrimeGap182.TypeIII.PrimitiveRadialFromParameter.Inputs.localCoverRules
#print axioms PrimeGap182.TypeIII.PrimitiveRadialFromParameter.Inputs.toPrimitiveInputs
