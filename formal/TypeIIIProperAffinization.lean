import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import TypeIIISchemeIdempotentClopens

/-!
# Actual affinization of a proper morphism to an affine scheme

For q : X → Spec R, the intermediate scheme is literally Spec Γ(X, ⊤).
The first morphism is the existing canonical X.toSpecΓ, and the second
is induced by the original map on global sections, composed with the
canonical identification R ≅ Γ(Spec R, ⊤).  Their composite is q.

If q is universally closed, the second morphism is integral and the
first is universally closed and surjective.  If q is proper, the first
morphism is proper.  Surjectivity uses the actual dominant affinization
map of a quasi-compact scheme and its proved closedness.  The canonical
clopen correspondence is retained for these same objects and maps.

No henselianity or nontriviality is assumed.  This constructs the
affinization factorization; it does not assert that its fibers are
connected, or that clopens lift from a proper scheme's closed fiber.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.ProperAffinization

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

/-- The actual spectrum of the original ring of global sections. -/
abbrev affineScheme (X : Scheme.{u}) : Scheme.{u} := Spec Γ(X, ⊤)

/-- The original canonical morphism into that spectrum. -/
def toAffinization (X : Scheme.{u}) : X ⟶ affineScheme X := X.toSpecΓ

/-- Its map on global sections is the existing canonical spectrum isomorphism. -/
theorem toAffinization_appTop (X : Scheme.{u}) :
    (toAffinization X).appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom :=
  Scheme.toSpecΓ_appTop X

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The original coefficient map R → Γ(X, ⊤), normalized by the canonical affine-base isomorphism. -/
def coefficient (q : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom

/-- The coefficient map evaluates by the original q.appTop after the canonical identification. -/
theorem coefficient_apply (q : X ⟶ Spec (.of R)) (r : R) :
    coefficient q r = q.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := rfl

/-- The algebra structure induced by this exact coefficient map, without a new global instance. -/
@[instance_reducible]
def coefficientAlgebra (q : X ⟶ Spec (.of R)) : Algebra R Γ(X, ⊤) :=
  (coefficient q).toAlgebra

/-- The induced algebra map is the original coefficient map. -/
theorem coefficientAlgebra_map (q : X ⟶ Spec (.of R)) :
    letI := coefficientAlgebra q
    algebraMap R Γ(X, ⊤) = coefficient q := rfl

/-- The actual spectrum morphism induced by the original coefficient map. -/
def toBase (q : X ⟶ Spec (.of R)) : affineScheme X ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (coefficient q))

/-- The unchanged original morphism factors through its actual affinization. -/
theorem factorization (q : X ⟶ Spec (.of R)) :
    toAffinization X ≫ toBase q = q := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop) = q
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The second morphism is affine because it is an actual spectrum morphism. -/
theorem toBase_isAffineHom (q : X ⟶ Spec (.of R)) : IsAffineHom (toBase q) := by
  unfold toBase
  infer_instance

/-- The second morphism is separated, with no properness hypothesis. -/
theorem toBase_isSeparated (q : X ⟶ Spec (.of R)) : IsSeparated (toBase q) := by
  let := toBase_isAffineHom q
  infer_instance

/-- Universal closedness of q makes its actual coefficient map integral. -/
theorem coefficient_isIntegral (q : X ⟶ Spec (.of R)) [UniversallyClosed q] :
    (coefficient q).IsIntegral := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom.IsIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed q

/-- The exact algebra induced by q is integral, with no replacement of the global-section ring. -/
theorem coefficientAlgebra_isIntegral (q : X ⟶ Spec (.of R)) [UniversallyClosed q] :
    letI := coefficientAlgebra q
    Algebra.IsIntegral R Γ(X, ⊤) := by
  let := coefficientAlgebra q
  exact algebraMap_isIntegral_iff.mp (coefficient_isIntegral q)

/-- The second morphism is integral when the original morphism is universally closed. -/
theorem toBase_isIntegralHom (q : X ⟶ Spec (.of R)) [UniversallyClosed q] :
    IsIntegralHom (toBase q) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  exact coefficient_isIntegral q

/-- Universal closedness of q descends to its canonical morphism into the affinization. -/
theorem toAffinization_universallyClosed (q : X ⟶ Spec (.of R)) [UniversallyClosed q] :
    UniversallyClosed (toAffinization X) := by
  let := toBase_isSeparated q
  let : UniversallyClosed (toAffinization X ≫ toBase q) := by
    rw [factorization]
    infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated (toAffinization X) (toBase q)

/-- If q is proper, its original canonical morphism into the affinization is proper. -/
theorem toAffinization_isProper (q : X ⟶ Spec (.of R)) [IsProper q] :
    IsProper (toAffinization X) := by
  let := toBase_isSeparated q
  let : IsProper (toAffinization X ≫ toBase q) := by
    rw [factorization]
    infer_instance
  exact IsProper.of_comp (toAffinization X) (toBase q)

/-- Universal closedness of q gives actual surjectivity of the canonical affinization morphism. -/
theorem toAffinization_surjective (q : X ⟶ Spec (.of R)) [UniversallyClosed q] :
    Surjective (toAffinization X) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let := toAffinization_universallyClosed q
  let : IsDominant (toAffinization X) := by
    change IsDominant X.toSpecΓ
    infer_instance
  infer_instance

/-- The literal canonical morphism identifies clopens, independently of properness. -/
def toAffinizationClopenOrderIso (X : Scheme.{u}) :
    Clopens (affineScheme X) ≃o Clopens X :=
  SchemeIdempotentClopens.toSpecΓClopenOrderIso X

/-- This clopen correspondence is inverse image by the same canonical factorization morphism. -/
theorem toAffinizationClopenOrderIso_apply (X : Scheme.{u}) (U : Clopens (affineScheme X)) :
    toAffinizationClopenOrderIso X U =
      SchemeIdempotentClopens.clopenPullback (toAffinization X) U := rfl

end PrimeGap182.TypeIII.ProperAffinization

#print axioms PrimeGap182.TypeIII.ProperAffinization.affineScheme
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization_appTop
#print axioms PrimeGap182.TypeIII.ProperAffinization.coefficient
#print axioms PrimeGap182.TypeIII.ProperAffinization.coefficient_apply
#print axioms PrimeGap182.TypeIII.ProperAffinization.coefficientAlgebra
#print axioms PrimeGap182.TypeIII.ProperAffinization.coefficientAlgebra_map
#print axioms PrimeGap182.TypeIII.ProperAffinization.toBase
#print axioms PrimeGap182.TypeIII.ProperAffinization.factorization
#print axioms PrimeGap182.TypeIII.ProperAffinization.toBase_isAffineHom
#print axioms PrimeGap182.TypeIII.ProperAffinization.toBase_isSeparated
#print axioms PrimeGap182.TypeIII.ProperAffinization.coefficient_isIntegral
#print axioms PrimeGap182.TypeIII.ProperAffinization.coefficientAlgebra_isIntegral
#print axioms PrimeGap182.TypeIII.ProperAffinization.toBase_isIntegralHom
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization_universallyClosed
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization_isProper
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinization_surjective
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinizationClopenOrderIso
#print axioms PrimeGap182.TypeIII.ProperAffinization.toAffinizationClopenOrderIso_apply
