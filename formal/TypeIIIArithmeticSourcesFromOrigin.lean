import TypeIIIArithmeticPrimitiveSources

/-!
# Primitive arithmetic sources from origin stalks

Katz's untwisted invariant-line statement and the general Tate-twist law
give q^-1 on the normalized origin stalk. General arithmetic comparison of
origin stalks with inertia invariants under scalar pullback then constructs
the original ScalarSourceModels record, including its common scalar.

The geometric source equivalences, origin comparisons, and Tate law are
explicit inputs. They must be realized for the same sheaves and coefficient
field as the rest of the proof. This module does not construct that model.
No assertion about Frobenius on the entire Kloosterman space is assumed.
Katz, GKM, Theorem 7.4.3, section 4.3, and section 11.0.1:
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped Classical Matrix

namespace PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin

open StartingSourceMaps ArithmeticSourceMaps ArithmeticSourceTransport
open ArithmeticPrimitiveSources RegularUnipotentRepresentation RegularUnipotentBoundary

universe u v w a b c d z

section ScalarGeometry

open MvPolynomial
variable (E : Type) [Field E]

/-- Extension of x ↦ a*x across the origin of the affine line over E. -/
def affineScalarHom (a : Eˣ) :
    MvPolynomial (Fin 1) E →ₐ[E] MvPolynomial (Fin 1) E :=
  aeval (fun _ => C (a : E) * X 0)

/-- Its restriction is the exact Laurent-ring map used by scalarSource. -/
theorem affine_scalar_restriction (a : Eˣ) :
    (localInputHom E E).comp (affineScalarHom E a) =
      (scalarHom E E a).comp (localInputHom E E) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  simp only [AlgHom.comp_apply, affineScalarHom, localInputHom,
    aeval_X, map_mul, aeval_C]
  change LaurentPolynomial.C (a : E) * LaurentPolynomial.T 1 =
    LaurentPolynomial.eval₂ LaurentPolynomial.C
      (constantUnit E a * PhysicalTorusLaurent.variableUnit E) (LaurentPolynomial.T 1)
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

/-- The extension fixes the origin as an E-valued point, including residues. -/
theorem affine_scalar_fixes_origin (a : Eˣ) :
    (aeval (fun _ : Fin 1 => (0 : E))).comp (affineScalarHom E a) =
      aeval (fun _ : Fin 1 => (0 : E)) := by
  ext i
  fin_cases i
  simp [affineScalarHom]

/-- The extension is invertible, with the inverse scalar as inverse map. -/
theorem affine_scalar_inverse (a : Eˣ) :
    (affineScalarHom E a).comp (affineScalarHom E a⁻¹) = AlgHom.id E _ := by
  ext i
  fin_cases i
  simp [affineScalarHom]

end ScalarGeometry

variable {G : Type d} [Group G]

/-- The exact vector used by ScalarSourceModels is inertia invariant. -/
theorem tame_first_vector_invariant (tame : G →* Multiplicative ℂ) :
    Pi.single (0 : Fin 3) (1 : ℂ) ∈ (tameRepresentation tame).invariants := by
  intro g
  change Matrix.toLin' (exponentialMatrix (tame g).toAdd) (Pi.single 0 1) = _
  ext i
  fin_cases i <;>
    simp [exponentialMatrix, regularMatrix, jordanThreeCoordinates,
      Matrix.toLin'_apply, Matrix.mulVec]

variable (K E : Type) [Field K] [Field E] [Algebra K E]
  {Line : Type u} [Category.{a} Line] {Input : Type v} [Category.{b} Input]
  {Local : Type w} [Category.{c} Local]
  {original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input}
  (P : Pullbacks (Local := Local) K E original) (J : Local ⥤ FDRep ℂ G)
  (LF : LocalFrobenius J)

/-- Degree-zero invariant stalk at the origin, with residue Frobenius.
In the intended model this is (j_* A)_0, even if an extension by zero is
used elsewhere. It is not the full nearby fiber of a ramified source. -/
structure OriginStalks (Line : Type u) where
  fiber : Line → ModuleCat.{z} ℂ
  frobenius : ∀ A, fiber A ≃ₗ[ℂ] fiber A

variable (O : OriginStalks.{u,z} Line)

/-- General arithmetic origin-stalk compatibility, for every source A
and every scalar automorphism x ↦ a*x. The residue point is fixed.
The comparison acts only on invariants; it does not equate full nearby
Frobenius operators for different scalar pullbacks. -/
structure ScalarStalkComparison where
  comparison : ∀ (A : Line) (a : Eˣ),
    Representation.invariants (J.obj (scalarSource K E P A a)).ρ ≃ₗ[ℂ] O.fiber A
  frobenius : ∀ (A : Line) (a : Eˣ)
      (v : Representation.invariants (J.obj (scalarSource K E P A a)).ρ),
    LF.action (scalarSource K E P A a) v =
      ((comparison A a).symm (O.frobenius A (comparison A a v)) :
        (J.obj (scalarSource K E P A a)).V)

variable (C : ScalarStalkComparison K E P J LF O)

include C in
/-- Scalar Frobenius on an origin stalk gives the same scalar on every
scalar-pullback invariant vector through the supplied general comparison. -/
theorem scalar_invariant_action (A : Line) (r : ℂ)
    (hscalar : ∀ v, O.frobenius A v = r • v) (a : Eˣ)
    (v : (J.obj (scalarSource K E P A a)).V)
    (hv : v ∈ Representation.invariants (J.obj (scalarSource K E P A a)).ρ) :
    LF.action (scalarSource K E P A a) v = r • v := by
  have h := C.frobenius A a ⟨v, hv⟩
  rw [hscalar, map_smul, LinearEquiv.symm_apply_apply] at h
  exact h

variable [Fintype E] (twistOne : Line → Line)

/-- General Tate twist (1) on the invariant stalk, for every source.
Only the arithmetic action changes, by the extension-cardinality inverse. -/
structure TateOriginRules where
  comparison : ∀ A, O.fiber (twistOne A) ≃ₗ[ℂ] O.fiber A
  frobenius : ∀ A v,
    comparison A (O.frobenius (twistOne A) v) =
      (Fintype.card E : ℂ)⁻¹ • O.frobenius A (comparison A v)

variable (T : TateOriginRules E O twistOne)

include T in
omit [Field E] [Category.{a} Line] in
/-- Katz's identity action on the raw invariant stalk becomes q^-1
after normalization; the conclusion quantifies over its entire stalk. -/
theorem normalized_origin_action (raw : Line)
    (hraw : ∀ v, O.frobenius raw v = v) (v : O.fiber (twistOne raw)) :
    O.frobenius (twistOne raw) v = (Fintype.card E : ℂ)⁻¹ • v := by
  apply (T.comparison raw).injective
  rw [T.frobenius, hraw, map_smul]

variable (raw as : Line) (tame : G →* Multiplicative ℂ)
  (klZero : ∀ a : Eˣ,
    Representation.Equiv (J.obj (scalarSource K E P (twistOne raw) a)).ρ
      (tameRepresentation tame))
  (asZero : ∀ a : Eˣ,
    Representation.Equiv (J.obj (scalarSource K E P as a)).ρ
      (Representation.trivial ℂ G ℂ))
  (hraw : ∀ v, O.frobenius raw v = v)
  (has : ∀ v, O.frobenius as v = v)

/-- Construct the original primitive arithmetic record. The raw and AS
origin actions, geometric models, and general comparisons are inputs;
the normalized common scalar and both arithmetic fields are derived. -/
def scalarSourceModels : ScalarSourceModels K E P J LF (twistOne raw) as tame where
  klZero := klZero
  asZero := asZero
  scalar := (Fintype.card E : ℂ)⁻¹
  scalar_ne_zero := inv_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))
  klLine a := by
    apply scalar_invariant_action K E P J LF O C (twistOne raw) _
      (normalized_origin_action E O twistOne T raw hraw)
    exact ((invariantsEquiv (klZero a)).symm
      ⟨Pi.single 0 1, tame_first_vector_invariant tame⟩).property
  asAction a v := by
    let w : Representation.invariants (J.obj (scalarSource K E P as a)).ρ :=
      (invariantsEquiv (asZero a)).symm ⟨asZero a v, fun _ => rfl⟩
    have hw : (w : (J.obj (scalarSource K E P as a)).V) = v :=
      (asZero a).toLinearEquiv.symm_apply_apply v
    have hv : v ∈ Representation.invariants (J.obj (scalarSource K E P as a)).ρ := hw ▸ w.property
    have h := scalar_invariant_action K E P J LF O C as 1
      (fun x => (has x).trans (one_smul ℂ x).symm) a v hv
    rw [h, one_smul]

/-- Origin inputs for one fixed raw source, its Tate twist and the AS
source. No normalized scalar or normalized arithmetic action is supplied. -/
structure Inputs where
  origin : OriginStalks.{u,z} Line
  comparison : ScalarStalkComparison K E P J LF origin
  tate : TateOriginRules E origin twistOne
  klZero : ∀ a : Eˣ,
    Representation.Equiv (J.obj (scalarSource K E P (twistOne raw) a)).ρ
      (tameRepresentation tame)
  asZero : ∀ a : Eˣ,
    Representation.Equiv (J.obj (scalarSource K E P as a)).ρ
      (Representation.trivial ℂ G ℂ)
  rawAction : ∀ v, origin.frobenius raw v = v
  asAction : ∀ v, origin.frobenius as v = v

variable {K E P J LF twistOne raw as tame}

/-- Apply the checked origin deduction to the same source objects and
local functors retained in the input bundle. -/
def Inputs.primitiveSources (S : Inputs K E P J LF twistOne raw as tame) :
    ScalarSourceModels K E P J LF (twistOne raw) as tame :=
  scalarSourceModels K E P J LF S.origin S.comparison twistOne S.tate
    raw as tame S.klZero S.asZero S.rawAction S.asAction

/-- The common normalization is fixed by the residue-field cardinality. -/
theorem Inputs.primitiveSources_scalar (S : Inputs K E P J LF twistOne raw as tame) :
    S.primitiveSources.scalar = (Fintype.card E : ℂ)⁻¹ := rfl

end PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin

#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.affine_scalar_restriction
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.affine_scalar_fixes_origin
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.affine_scalar_inverse
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.tame_first_vector_invariant
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.scalar_invariant_action
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.normalized_origin_action
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.scalarSourceModels
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.Inputs.primitiveSources
#print axioms PrimeGap182.TypeIII.ArithmeticSourcesFromOrigin.Inputs.primitiveSources_scalar
