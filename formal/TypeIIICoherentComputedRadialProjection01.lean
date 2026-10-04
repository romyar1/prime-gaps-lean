import TypeIIIPublishedUniformComplexity

/-!
# General standard projection with computed radial observables

This GENERAL interface binds the radial predicate/set to one given inertia
realization by DEFINITION. It does not prove the supplied operators are the
adic standard theory. The LocalRules input concerns ALL eligible objects;
no physical-family profile, exclusion, or estimate is assumed.
-/

noncomputable section

namespace PrimeGap182.TypeIII.CoherentComputedRadialProjection01

open PublishedSupportRules PublishedFourierRules PublishedTypeIII
open PublishedApplicationBridge PublishedPhaseApplication

universe u v w a b

variable {p : ℕ} [Fact p.Prime]
  {Obj : Type u} {CurveObj : Type v}
  {E : Type a} [Field E] {G : Type b} [Group G]

/-- The three operators remain those of F. Only the two observers are
computed from the SAME actual radial realization. -/
def computedFourierData
    (F : FourierData (AlgebraicClosure (ZMod p)) Obj CurveObj)
    (PD : PhaseData (AlgebraicClosure (ZMod p)) E G)
    (radial : Obj → FDRep E G) :
    FourierData (AlgebraicClosure (ZMod p)) Obj CurveObj :=
  { F with
    HasSimpleRadialPhases := fun P => PD.HasProfile (radial P)
    phases := fun P => PD.phases (radial P) }

/-- All non-radial data, qualitative operations and whole arithmetic lifts
are unchanged. The general LocalRules must have their actual computed
radial meaning; no arbitrary interpretation predicate is accepted. -/
def computedTheory (T : Theory.{u,v} p)
    (PD : PhaseData (AlgebraicClosure (ZMod p)) E G)
    (radial : T.Obj → FDRep E G)
    (localLaws : LocalRules T.data T.coefficient
      (computedFourierData T.fourier PD radial)) : Theory.{u,v} p :=
  { T with
    fourier := computedFourierData T.fourier PD radial
    localRules := localLaws
    traceWeights := T.traceWeights }

/-- The two former recognition cuts are identities of definitions. -/
def computedRadialRealization (T : Theory.{u,v} p)
    (PD : PhaseData (AlgebraicClosure (ZMod p)) E G)
    (radial : T.Obj → FDRep E G)
    (localLaws : LocalRules T.data T.coefficient
      (computedFourierData T.fourier PD radial)) :
    RadialRealization (computedTheory T PD radial localLaws) PD where
  inertia := radial
  profile := fun _ => Iff.rfl
  phases := fun _ => rfl

/-- Replacing the numerical QST witnesses leaves the SAME computed
radial observers unchanged. This avoids identifying different whole
Theory records merely because their qualitative operations agree. -/
def computedUniformRadialRealization (T : Theory.{u,v} p)
    (PD : PhaseData (AlgebraicClosure (ZMod p)) E G)
    (radial : T.Obj → FDRep E G)
    (localLaws : LocalRules T.data T.coefficient
      (computedFourierData T.fourier PD radial))
    (bnd : PublishedUniformComplexity.Bounds)
    (UR : PublishedUniformComplexity.Rules bnd (computedTheory T PD radial localLaws)) :
    RadialRealization UR.theory PD where
  inertia := radial
  profile := fun _ => Iff.rfl
  phases := fun _ => rfl

end PrimeGap182.TypeIII.CoherentComputedRadialProjection01

#print axioms PrimeGap182.TypeIII.CoherentComputedRadialProjection01.computedFourierData
#print axioms PrimeGap182.TypeIII.CoherentComputedRadialProjection01.computedTheory
#print axioms PrimeGap182.TypeIII.CoherentComputedRadialProjection01.computedRadialRealization

#print axioms PrimeGap182.TypeIII.CoherentComputedRadialProjection01.computedUniformRadialRealization
