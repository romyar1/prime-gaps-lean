import TypeIIISourceCohomologyInputs

/-!
# Use the published compact-lissity corollary as a general input

On the fixed product compactification P1 × S with boundary 0 and infinity,
a lisse adic sheaf of constant total boundary conductor has lisse R1 f!.
This is the adic corollary of Deligne--Laumon 2.1.1(ii), 2.1.2 and the
integral ULA passage in Hansen--Scholze, proof of Proposition 3.8.

The corollary applies to every lisse object satisfying conductor constancy;
it is not the Type III input's lissity or conductor calculation. The latter
remain checked applications. The previous finite/lattice/adic derivation
can still supply this general input through the adapter below.

This explicitly enlarges the published assumption boundary, avoiding a
separate construction of finite coefficient categories in each source
realization. It does not assert existence of the remaining source data.
-/

noncomputable section
open CategoryTheory

namespace PrimeGap182.TypeIII.PublishedCohomologyCorollary

open PublishedPhysicalConstruction OrdinaryBaseChangeFromDuality
open CompactLissityFromFiniteCoefficients

universe u v w z a b
variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C) (P : ParameterData C)

/-- General compact-lissity corollary plus the unchanged eight physical
cohomology laws. Each law still quantifies over arbitrary input objects. -/
structure PhysicalInputs : Prop where
  compact : CompactLissityRules D (H := H) (P := P)
  other : OtherCohomologyRules D H P

variable {D H P}

/-- The old, more detailed finite-to-adic proof remains a sufficient route. -/
theorem PhysicalInputs.ofFinite
    (S : SourceCohomologyInputs.PhysicalInputs.{u,v,w,z,a,b} D H P) :
    PhysicalInputs D H P :=
  ⟨S.toCompactInputs.compactRules, S.otherRules⟩

/-- Keep the original cohomology interface consumed by the family proofs. -/
theorem PhysicalInputs.cohomologyRules (S : PhysicalInputs D H P) :
    CohomologyRules D H P where
  compact_lisse := S.compact.compact_lisse
  ordinary_duality := S.other.ordinary_duality
  dualTate_lisse := S.other.dualTate_lisse
  lisse_of_iso := S.other.lisse_of_iso
  image_lisse := S.other.image_lisse
  image_pure := S.other.image_pure
  signed_lisse := S.other.signed_lisse
  signed_pure := S.other.signed_pure
  dualTate_pure := S.other.dualTate_pure

end PrimeGap182.TypeIII.PublishedCohomologyCorollary

#print axioms PrimeGap182.TypeIII.PublishedCohomologyCorollary.PhysicalInputs.ofFinite
#print axioms PrimeGap182.TypeIII.PublishedCohomologyCorollary.PhysicalInputs.cohomologyRules
