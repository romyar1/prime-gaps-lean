import TypeIIIGenericCompactLissity

/-!
# Cohomology source inputs with the compact-lissity conclusions derived

These records retain the actual finite-coefficient category, lattice levels,
and general finite/adic laws. The existing finite-to-adic proof constructs
compact lissity. Physical inputs also retain the other cohomology laws;
generic local inputs do not require them. Neither record stores a complete
`CohomologyRules` or a completed compact-lissity conclusion.

Existence of the compatible finite and adic models remains an input.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.SourceCohomologyInputs

open PublishedPhysicalConstruction CompactLissityFromFiniteCoefficients
open OrdinaryBaseChangeFromDuality

universe u v w z a b

variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C) (P : ParameterData C)

/-- General finite, lattice and adic inputs on one fixed compactification.
The finite objects and their laws belong to the same chosen category. -/
structure CompactInputs where
  Finite : Type a
  [finiteCategory : Category.{b} Finite]
  [finiteAbelian : Abelian Finite]
  finiteData : FiniteData Finite Point
  lattice : LatticeData Input (F := Finite)
  finiteRules : FiniteRules finiteData
  latticeRules : LatticeRules D finiteData lattice
  adicRules : AdicRules D H P finiteData lattice

/-- Physical cohomology still requires its other eight original laws.
Compact lissity itself is obtained from the supplied finite/adic inputs. -/
structure PhysicalInputs extends CompactInputs.{u, v, w, z, a, b} D H P where
  otherRules : OtherCohomologyRules D H P

variable {D H P}

/-- The exact one-field interface consumed by generic ordinary base change. -/
theorem CompactInputs.compactRules (S : CompactInputs D H P) :
    CompactLissityRules D (H := H) (P := P) := by
  let := S.finiteCategory
  let := S.finiteAbelian
  exact GenericCompactLissity.compactLissityRules S.finiteRules S.latticeRules S.adicRules

/-- The full physical interface, with compact lissity proved internally. -/
theorem PhysicalInputs.cohomologyRules (S : PhysicalInputs D H P) :
    CohomologyRules D H P := by
  let := S.finiteCategory
  let := S.finiteAbelian
  exact CompactLissityFromFiniteCoefficients.cohomologyRules
    S.finiteRules S.latticeRules S.adicRules S.otherRules

end PrimeGap182.TypeIII.SourceCohomologyInputs

#print axioms PrimeGap182.TypeIII.SourceCohomologyInputs.CompactInputs.compactRules
#print axioms PrimeGap182.TypeIII.SourceCohomologyInputs.PhysicalInputs.cohomologyRules
