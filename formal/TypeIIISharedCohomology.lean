import TypeIIIPublishedCohomologyCorollary
import TypeIIIPulledCurveInput

/-!
# Cohomology application on shared dual and pullback operations

Parameter dual(-1) is the selected contravariant functor used by relative
duality. Thus the ordinary-duality existence clause is an application of
the same guarded isomorphism, not an independent theorem input.
Compact base change reuses the curve pullback's lissity, tameness, slope
and dual comparison; only the two cohomology comparisons remain separate.
The general published relative-duality, compact-lissity, purity and
base-change laws remain explicit. No new external mathematical law is added.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.SharedCohomology
open PublishedPhysicalConstruction OrdinaryBaseChangeFromDuality PulledCurveInput

universe u v w z a b c d e k

/-- Parameter observables and signing, without a second choice of dual(-1). -/
structure ParameterObservables (C : Type w) where
  Lisse : C → Prop
  Pure : C → ℝ → Prop
  signed : C → C

variable {C : Type w} [Category.{z} C]
  (O : ParameterObservables C) (DT : Cᵒᵖ ⥤ C)

/-- Read dual(-1) from the functor in relative duality and base change. -/
def ParameterObservables.data : ParameterData C where
  Lisse := O.Lisse
  Pure := O.Pure
  signed := O.signed
  dualTateMinusOne A := DT.obj (Opposite.op A)

variable {Input : Type u} {Point : Type v} [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C) (P : ParameterData C)

/-- The remaining general cohomology rules, excluding the duplicate
ordinary-duality existence clause. All original guards are retained. -/
structure OtherRules : Prop where
  dualTate_lisse : ∀ A, P.Lisse A → P.Lisse (P.dualTateMinusOne A)
  lisse_of_iso : ∀ A B, Nonempty (A ≅ B) → P.Lisse B → P.Lisse A
  image_lisse : ∀ A B (f : A ⟶ B), P.Lisse A → P.Lisse B →
    P.Lisse (Abelian.image f)
  image_pure : ∀ A a, D.Lisse A → D.Pure A a →
    D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact A) → P.Lisse (H.compact (D.dual A)) →
      P.Pure (parabolicCore H A) (a + 1)
  signed_lisse : ∀ A, P.Lisse A → P.Lisse (P.signed A)
  signed_pure : ∀ A a, P.Pure A a → P.Pure (P.signed A) a
  dualTate_pure : ∀ A a, P.Lisse A → P.Pure A a →
    P.Pure (P.dualTateMinusOne A) (2 - a)

variable {D H}

/-- Apply precisely the relative-duality map used by base change,
with the original lissity and positive-slope premises unchanged. -/
theorem physicalInputs
    (S : RelativeDuality D (H := H) (P := O.data DT) DT)
    (compact : CompactLissityRules D (H := H) (P := O.data DT))
    (R : OtherRules D H (O.data DT)) :
    PublishedCohomologyCorollary.PhysicalInputs D H (O.data DT) where
  compact := compact
  other := {
    ordinary_duality := fun A hl hs hc => ⟨S.duality A hl hs hc⟩
    dualTate_lisse := R.dualTate_lisse
    lisse_of_iso := R.lisse_of_iso
    image_lisse := R.image_lisse
    image_pure := R.image_pure
    signed_lisse := R.signed_lisse
    signed_pure := R.signed_pure
    dualTate_pure := R.dualTate_pure }

variable [Category.{k} Input] {Input' : Type a} [Category.{e} Input']
  {Point' : Type b} {C' : Type c} [Category.{d} C'] [Abelian C']
  (D' : CurveData Input' Point') (H' : CohomologyData Input' C')
  (DT' : C'ᵒᵖ ⥤ C') (B : C ⥤ C') (pull : Input ⥤ Input')

/-- The compact and parameter-dual comparisons. Preservation of curve
properties and the curve-dual comparison come from the same pullback laws
already used to construct the three-factor source. -/
structure BaseChangeComparisons where
  compact : ∀ A, D.Lisse A → (B.obj (H.compact A) ≅ H'.compact (pull.obj A))
  dualTate : ∀ V, P.Lisse V →
    (B.obj (DT.obj (Opposite.op V)) ≅ DT'.obj (Opposite.op (B.obj V)))

variable {P DT H' DT' B pull}

/-- Reuse the exact curve-dual isomorphism in compact and ordinary
base change, instead of supplying a second unrelated comparison. -/
def BaseChangeComparisons.compactBaseChange
    (M : BaseChangeComparisons (D := D) (H := H) DT P H' DT' B pull)
    (R : PullbackProperties D D' pull) :
    CompactBaseChange D DT D' DT' B pull.obj (H := H) (H' := H') (P := P) where
  lisse := R.lisse
  tame := R.tame
  slope A := R.slope A 1
  dual := R.dual
  compact := M.compact
  dualTate := M.dualTate

end PrimeGap182.TypeIII.SharedCohomology

#print axioms PrimeGap182.TypeIII.SharedCohomology.ParameterObservables.data
#print axioms PrimeGap182.TypeIII.SharedCohomology.physicalInputs
#print axioms PrimeGap182.TypeIII.SharedCohomology.BaseChangeComparisons.compactBaseChange
