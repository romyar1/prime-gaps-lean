import TypeIIIStartingSourceComplexity

/-!
# The physical family under the actual radial substitution

The map (T,z) -> (T^2,z*T^2), followed by the existing physical map,
is the scheme morphism with parameters (m/(n*z^3), m*T^2/(alpha*z)).
This is proved on coordinate rings and hence on schemes, over arbitrary
coefficient algebras. Pullback composition then identifies the radial
restriction of the existing signed parabolic core with this explicit map.

This supplies geometric coordinate compatibility, not a construction of
local Fourier functors, inertia, or the finite-origin comparison maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.PhysicalRadialMorphism

open PhysicalTorusMorphism PhysicalTorusLaurent

universe u v w z
variable (K : Type u) [Field K]
variable {A : Type u} [CommRing A] [Algebra K A]

def radialParameters (T z : Aˣ) : Aˣ × Aˣ := (T ^ 2, z * T ^ 2)

def radialPhysicalParameters (α m n : Kˣ) (T z : Aˣ) : Aˣ × Aˣ :=
  (Units.map (algebraMap K A) (m / n) / z ^ 3,
    Units.map (algebraMap K A) (m / α) * T ^ 2 / z)

/-- Exact cancellation is valid in units of any commutative algebra. -/
theorem mappedParameters_radial (α m n : Kˣ) (T z : Aˣ) :
    mappedParameters K α m n (radialParameters T z).1 (radialParameters T z).2 =
      radialPhysicalParameters K α m n T z := by
  apply Prod.ext <;>
    dsimp [mappedParameters, radialParameters, radialPhysicalParameters] <;>
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev] <;> group

def radialEnd : TorusRing K →ₐ[K] TorusRing K :=
  evaluation (radialParameters (xUnit K) (yUnit K)).1
    (radialParameters (xUnit K) (yUnit K)).2

def radialPhysicalEnd (α m n : Kˣ) : TorusRing K →ₐ[K] TorusRing K :=
  evaluation (radialPhysicalParameters K α m n (xUnit K) (yUnit K)).1
    (radialPhysicalParameters K α m n (xUnit K) (yUnit K)).2

/-- The ring-map identity underlying radial restriction of the physical family. -/
theorem radialEnd_comp_physicalEnd (α m n : Kˣ) :
    (radialEnd K).comp (physicalEnd K α m n) = radialPhysicalEnd K α m n := by
  unfold radialEnd
  rw [evaluation_comp_physicalEnd, mappedParameters_radial]
  rfl

theorem evaluation_comp_radialEnd (T z : Aˣ) :
    (evaluation (K := K) T z).comp (radialEnd K) =
      evaluation (radialParameters T z).1 (radialParameters T z).2 := by
  rw [radialEnd, evaluation_natural]
  simp only [radialParameters, map_mul, map_pow]
  have hx : Units.map (evaluation (K := K) T z).toRingHom.toMonoidHom (xUnit K) = T :=
    map_evaluation_xUnit T z
  have hy : Units.map (evaluation (K := K) T z).toRingHom.toMonoidHom (yUnit K) = z :=
    map_evaluation_yUnit T z
  rw [hx, hy]

theorem evaluation_comp_radialPhysicalEnd (α m n : Kˣ) (T z : Aˣ) :
    (evaluation (K := K) T z).comp (radialPhysicalEnd K α m n) =
      evaluation (radialPhysicalParameters K α m n T z).1
        (radialPhysicalParameters K α m n T z).2 := by
  rw [← radialEnd_comp_physicalEnd, ← AlgHom.comp_assoc, evaluation_comp_radialEnd,
    evaluation_comp_physicalEnd, mappedParameters_radial]

def radialMorphism : torusScheme K ⟶ torusScheme K :=
  Spec.map (CommRingCat.ofHom (radialEnd K).toRingHom)

def radialPhysicalMorphism (α m n : Kˣ) : torusScheme K ⟶ torusScheme K :=
  Spec.map (CommRingCat.ofHom (radialPhysicalEnd K α m n).toRingHom)

/-- Equality of genuine morphisms, not an equality inferred from rational points. -/
theorem radialMorphism_physicalMorphism (α m n : Kˣ) :
    radialMorphism K ≫ physicalMorphism K α m n = radialPhysicalMorphism K α m n := by
  have h := congrArg AlgHom.toRingHom (radialEnd_comp_physicalEnd K α m n)
  dsimp only [radialMorphism, physicalMorphism, radialPhysicalMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h

theorem schemePoint_radialPhysicalMorphism (α m n : Kˣ) (T z : Aˣ) :
    schemePoint (K := K) T z ≫ radialPhysicalMorphism K α m n =
      schemePoint (radialPhysicalParameters K α m n T z).1
        (radialPhysicalParameters K α m n T z).2 := by
  have h := congrArg AlgHom.toRingHom (evaluation_comp_radialPhysicalEnd K α m n T z)
  dsimp only [schemePoint, radialPhysicalMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h

section FieldValues

variable {L : Type u} [Field L] [Algebra K L]

theorem radialPhysicalParameters_values (α m n : Kˣ) (T z : Lˣ) :
    ((radialPhysicalParameters K α m n T z).1 : L) =
        algebraMap K L (m : K) / (algebraMap K L (n : K) * (z : L) ^ 3) ∧
      ((radialPhysicalParameters K α m n T z).2 : L) =
        algebraMap K L (m : K) * (T : L) ^ 2 / (algebraMap K L (α : K) * z) := by
  simp [radialPhysicalParameters, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The xi-coordinate has exactly the T^2/A normalization used by Fu's rule. -/
theorem radial_xi_normalization (α m n : Kˣ) (T z : Lˣ) :
    ((radialPhysicalParameters K α m n T z).2 : L) =
      (T : L) ^ 2 / (algebraMap K L (α : K) * z / algebraMap K L (m : K)) := by
  rw [(radialPhysicalParameters_values K α m n T z).2]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end FieldValues

section GenericAngularPoint

open PublishedPhaseApplication

def angularUnit : (PhaseField K)ˣ := Units.mk0 (direction K) direction_ne_zero

/-- The actual xi-coordinate agrees with the normalization in the existing
local Fourier application, using its same transcendental direction. -/
theorem radial_xi_eq_Fu_scale (α m n : Kˣ) (T : (PhaseField K)ˣ) :
    ((radialPhysicalParameters K α m n T (angularUnit K)).2 : PhaseField K) =
      (T : PhaseField K) ^ 2 / radialScale (α : K) (m : K) := by
  exact radial_xi_normalization K α m n T (angularUnit K)

/-- The radial physical morphism itself avoids lambda=1 at the generic
angular point. This uses transcendence, not a restriction on T. -/
theorem radial_lambda_ne_one (α m n : Kˣ) (T : (PhaseField K)ˣ) :
    ((radialPhysicalParameters K α m n T (angularUnit K)).1 : PhaseField K) ≠ 1 := by
  rw [(radialPhysicalParameters_values K α m n T (angularUnit K)).1]
  change algebraMap K (PhaseField K) (m : K) /
    (algebraMap K (PhaseField K) (n : K) * direction K ^ 3) ≠ 1
  have hn : algebraMap K (PhaseField K) (n : K) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap K (PhaseField K)).injective.ne (Units.ne_zero n)
  intro h
  have he := (div_eq_one_iff_eq (mul_ne_zero hn (pow_ne_zero 3 direction_ne_zero))).mp h
  apply direction_pow_ne_constant 3 (by decide) ((m : K) / (n : K))
  rw [map_div₀, eq_div_iff hn]
  exact (mul_comm _ _).trans he.symm

end GenericAngularPoint

section PhysicalConstruction

open PublishedPhysicalConstruction

variable {p : ℕ} [Fact p.Prime] {C : Type w} [Category.{z} C]

/-- The usual contravariant composition isomorphism for pullback functors,
for every pair of maps. No Type III family is part of this general datum. -/
structure PullbackComposition (O : TorusOperationData p C) where
  comparison : ∀ (g h : torusScheme (ZMod p) ⟶ torusScheme (ZMod p)),
    O.pullback (g ≫ h) ≅ O.pullback h ⋙ O.pullback g

variable {Input : Type u} {Point : Type v}
  [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}

/-- Radial restriction of the SAME existing entry is pullback of its signed
parabolic core by the proved explicit radial physical map. -/
def radialPulledEntryIso (S : KloostermanInputData D) (O : TorusOperationData p C)
    (F : PullbackComposition O) (α m n : (ZMod p)ˣ) :
    (O.pullback (radialMorphism (ZMod p))).obj (pulledEntry (H := H) (P := P) S O α m n) ≅
      (O.pullback (radialPhysicalMorphism (ZMod p) α m n)).obj
        (P.signed (parabolicCore H S.input)) := by
  rw [← radialMorphism_physicalMorphism]
  exact ((F.comparison (radialMorphism (ZMod p)) (physicalMorphism (ZMod p) α m n)).app
    (P.signed (parabolicCore H S.input))).symm

end PhysicalConstruction
end PrimeGap182.TypeIII.PhysicalRadialMorphism

#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.mappedParameters_radial
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radialEnd_comp_physicalEnd
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.evaluation_comp_radialEnd
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.evaluation_comp_radialPhysicalEnd
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radialMorphism_physicalMorphism
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.schemePoint_radialPhysicalMorphism
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radialPhysicalParameters_values
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radial_xi_normalization
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radial_xi_eq_Fu_scale
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radial_lambda_ne_one
#print axioms PrimeGap182.TypeIII.PhysicalRadialMorphism.radialPulledEntryIso
