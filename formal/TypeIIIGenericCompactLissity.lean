import TypeIIICompactLissityFromFiniteCoefficients
import TypeIIIOrdinaryBaseChangeFromDuality

/-!
# The generic local stage needs only compact lissity

The finite-to-adic derivation supplies the smaller interface now consumed
by ordinary base change and `SourceData.GC'`. No generic pure-image, sign,
image-lissity, or dual-Tate-purity input is required. Actual relative
duality and pairing naturality are still supplied separately.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.GenericCompactLissity

open PublishedPhysicalConstruction CompactLissityFromFiniteCoefficients
open OrdinaryBaseChangeFromDuality

universe u v w z a b

/-- Populate the exact smaller interface from the existing finite-to-adic
proof, with no complete `CohomologyRules` or purity premise. -/
theorem compactLissityRules {Input : Type u} {Point : Type v} {F : Type a} {C : Type w}
    [Category.{b} F] [Abelian F] [Category.{z} C] [Abelian C]
    {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
    {T : FiniteData F Point} {M : LatticeData Input (F := F)}
    (finite : FiniteRules T) (lattice : LatticeRules D T M)
    (adic : AdicRules D H P T M) : CompactLissityRules D (H := H) (P := P) :=
  ⟨CompactLissityFromFiniteCoefficients.compact_lisse finite lattice adic⟩

end PrimeGap182.TypeIII.GenericCompactLissity

#print axioms PrimeGap182.TypeIII.GenericCompactLissity.compactLissityRules
