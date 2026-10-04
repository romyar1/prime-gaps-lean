import TypeIIINearbyFromStalkPullback

/-!
# Middle infinity from ordinary extension and perverse cohomology

The total middle functor is ordinary extension followed by pH0(-[1]).
General generic-restriction laws for these two functors give its infinity
comparison. The cycle sequence uses the same perverse generic-stalk
functor, so no independent middle-infinity identification is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.MiddleInfinityFromPerverse
open PublishedPhysicalConstruction PublishedPhaseApplication PublishedLocalConstruction
open CanonicalLocalCorrelation SourceInverseImageSystem NearbyFromStalkPullback TensorListRepresentation

universe u v q w t mu

section Middle
variable {C : Type u} [Category.{v} C] {Q : Type q} [Category.{w} Q]
  {I : Type t} [Group I] (Jinf : C ⥤ FDRep ℂ I)

/-- General ordinary extension, perverse cohomology of the shift, and
infinity stalks on their own domains. The two comparisons concern every
object of the appropriate domain, before the middle composite is formed. -/
structure Data where
  Ambient : Type u
  [ambientCategory : Category.{v} Ambient]
  [ambientAbelian : Abelian Ambient]
  extend : C ⥤ Ambient
  perverseShift : Ambient ⥤ Q
  ordinaryInfinity : Ambient ⥤ FDRep ℂ I
  perverseInfinity : Q ⥤ FDRep ℂ I
  extension : extend ⋙ ordinaryInfinity ≅ Jinf
  shift : perverseShift ⋙ perverseInfinity ≅ ordinaryInfinity

attribute [instance] Data.ambientCategory Data.ambientAbelian

variable {Jinf} (M : Data (Q := Q) Jinf)

/-- The actual total middle functor, on ambient constructible sheaves. -/
abbrev Data.middle : C ⥤ Q := M.extend ⋙ M.perverseShift

/-- Compose the general restriction laws on the same functors. -/
def Data.infinityComparison : M.middle ⋙ M.perverseInfinity ≅ Jinf :=
  NatIso.ofComponents (fun A => M.shift.app (M.extend.obj A) ≪≫ M.extension.app A)
    (by
      intro A B f
      have h₁ := M.shift.hom.naturality (M.extend.map f)
      change M.perverseInfinity.map (M.perverseShift.map (M.extend.map f)) ≫
        (M.shift.app (M.extend.obj B)).hom =
        (M.shift.app (M.extend.obj A)).hom ≫ M.ordinaryInfinity.map (M.extend.map f) at h₁
      have h₂ := M.extension.hom.naturality f
      change M.ordinaryInfinity.map (M.extend.map f) ≫ (M.extension.app B).hom =
        (M.extension.app A).hom ≫ Jinf.map f at h₂
      change M.perverseInfinity.map (M.perverseShift.map (M.extend.map f)) ≫
        ((M.shift.app (M.extend.obj B)).hom ≫ (M.extension.app B).hom) =
        ((M.shift.app (M.extend.obj A)).hom ≫ (M.extension.app A).hom) ≫ Jinf.map f
      rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc])

/-- The comparison is natural for every original source morphism. -/
theorem Data.infinity_natural {A B : C} (f : A ⟶ B) :
    M.perverseInfinity.map (M.middle.map f) ≫ (M.infinityComparison.app B).hom =
      (M.infinityComparison.app A).hom ≫ Jinf.map f :=
  M.infinityComparison.hom.naturality f

end Middle

variable {K : Type} [Field K] (B : System.{0,mu} K)
  {I : Type t} [Group I] {G : Type mu} [Group G]
  (L : FiniteOriginFromRestriction.Data K ℂ I G)
  (J : B.Obj .parameter ⥤ FDRep ℂ G)
  {Q : Type q} [Category.{w} Q]
  (perverseInfinity : Q ⥤ FDRep ℂ I)

/-- The general cycle arrows and local-transform identification, with
infinity fixed to the existing perverse generic-stalk functor. -/
structure CycleData (nearby : Q → FDRep ℂ L.Raw) where
  infinity_admissible : ∀ P, L.Admissible (perverseInfinity.obj P)
  vanishing : Q → FDRep ℂ L.Raw
  closedStalk : Q → FGModuleCat ℂ
  nearbyToVanishing : ∀ P, Representation.IntertwiningMap (nearby P).ρ (vanishing P).ρ
  vanishingToClosed : ∀ P, Representation.IntertwiningMap (vanishing P).ρ
    (geometricClosedStalk L.Raw (closedStalk P)).ρ
  localComparison : ∀ P, Representation.Equiv (vanishing P).ρ
    (L.unscaled.obj (perverseInfinity.obj P) (infinity_admissible P)).ρ
  exactness : ∀ P, LinearMap.range (nearbyToVanishing P).toLinearMap =
    LinearMap.ker (vanishingToClosed P).toLinearMap

/-- One global Fourier source and its cycle sequence on the same infinity
functor as the middle construction. All original cycle arrows are retained. -/
structure OriginInputs where
  fourier : Q ⥤ B.Obj .parameter
  stalk : StalkPullback B L J
  sequence : CycleData L perverseInfinity (fun P => stalk.raw.obj (fourier.obj P))

variable {B L J perverseInfinity}

/-- Construct the previous origin interface with this shared infinity. -/
abbrev OriginInputs.originData (O : OriginInputs B L J perverseInfinity) :
    OriginData B L J Q where
  fourier := O.fourier.obj
  stalk := O.stalk
  sequence := {
    infinity := perverseInfinity.obj
    infinity_admissible := O.sequence.infinity_admissible
    vanishing := O.sequence.vanishing
    closedStalk := O.sequence.closedStalk
    nearbyToVanishing := O.sequence.nearbyToVanishing
    vanishingToClosed := O.sequence.vanishingToClosed
    localComparison := O.sequence.localComparison
    exactness := O.sequence.exactness }

/-- Normalization retains this same infinity representation exactly. -/
theorem OriginInputs.infinity_eq (O : OriginInputs B L J perverseInfinity) (P : Q) :
    (O.originData.cycles.normalized L).finiteOriginData.infinity P =
      perverseInfinity.obj P := rfl

variable {Jinf : B.Obj .localCurve ⥤ FDRep ℂ I} [Jinf.Monoidal]
  (M : Data (Q := Q) Jinf) (O : OriginInputs B L J M.perverseInfinity)
  (ops : SheafOperations (PhaseField K) (B.Obj .localCurve) Q)
  (hmiddle : ops.middleExtension = M.middle)
  (dual : ∀ A, Representation.Equiv (Jinf.obj (ops.dual A)).ρ
    (dualRepresentation (Jinf.obj A)).ρ)

/-- Derive the former middle-extension comparison; ordinary local dual
restriction remains its separate general law. -/
def Data.infinityCompatibility : InfinityCompatibility ops Jinf
    (O.originData.cycles.normalized L).finiteOriginData where
  dual := dual
  middleExtension A := by
    change Representation.Equiv (M.perverseInfinity.obj (ops.middleExtension.obj A)).ρ (Jinf.obj A).ρ
    rw [hmiddle]
    exact equivOfIso (M.infinityComparison.app A)

end PrimeGap182.TypeIII.MiddleInfinityFromPerverse

#print axioms PrimeGap182.TypeIII.MiddleInfinityFromPerverse.Data.middle
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromPerverse.Data.infinityComparison
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromPerverse.Data.infinity_natural
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromPerverse.OriginInputs.originData
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromPerverse.OriginInputs.infinity_eq
#print axioms PrimeGap182.TypeIII.MiddleInfinityFromPerverse.Data.infinityCompatibility
