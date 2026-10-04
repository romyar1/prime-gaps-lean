import TypeIIIStartingSourceComplexity

/-!
# The canonical starting curve input

The existing KloostermanInputData is now constructed from the three actual
maps x, lambda*x, xi*x and the two one-variable source objects. The maps
are proved to be scalar pullbacks with coefficients in the parameter
torus ring; the coefficient cannot depend on the curve variable x.

General scalar-pullback rules transfer the one-variable source properties.
The resulting input is definitionally the recipe used in the complexity
calculation. No family-specific IdentifiesInputs premise is required.

The one-variable Kl3 properties are the normalized (twist (1)) rank-three
case of Katz, GKM, Theorems 4.1.1 and 7.4.3. The AS properties are for a
nontrivial additive character. These source properties and the general
scalar-pullback rules remain explicit published inputs; this does not
construct an adic sheaf category or supply local Fourier compatibility.
Reference: https://web.math.princeton.edu/~nmk/Katz-GKM.pdf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical MonoidalCategory

namespace PrimeGap182.TypeIII.CanonicalCurveInput

open StartingSourceMaps StartingSourceComplexity PublishedPhysicalConstruction
open PublishedConstructionComplexity PublishedPolynomialComplexity

universe u v w z a b
variable (k : Type u) [Field k]

/-- Pullback from the parameter torus (lambda,xi), omitting the curve x. -/
def parameterHom : PhysicalTorusMorphism.TorusRing k →ₐ[k] SourceRing k :=
  PhysicalTorusMorphism.evaluation (coordinateUnit k 1) (coordinateUnit k 2)

def coefficients : Fin 3 → (PhysicalTorusMorphism.TorusRing k)ˣ :=
  ![1, PhysicalTorusMorphism.xUnit k, PhysicalTorusMorphism.yUnit k]

def scalarHom (c : (PhysicalTorusMorphism.TorusRing k)ˣ) :
    MvPolynomial (Fin 1) k →ₐ[k] SourceRing k :=
  aeval (fun _ => ((Units.map (parameterHom k).toRingHom c : (SourceRing k)ˣ) : SourceRing k) *
    (coordinateUnit k 0 : SourceRing k))

def scalarMorphism (c : (PhysicalTorusMorphism.TorusRing k)ˣ) :
    sourceScheme k ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (scalarHom k c).toRingHom)

theorem parameterHom_xUnit :
    Units.map (parameterHom k).toRingHom (PhysicalTorusMorphism.xUnit k) =
      coordinateUnit k 1 :=
  PhysicalTorusMorphism.map_evaluation_xUnit _ _

theorem parameterHom_yUnit :
    Units.map (parameterHom k).toRingHom (PhysicalTorusMorphism.yUnit k) =
      coordinateUnit k 2 :=
  PhysicalTorusMorphism.map_evaluation_yUnit _ _

/-- Equality of the actual ring maps with parameter-unit scalar maps. -/
theorem inputHom_eq_scalarHom (i : Fin 3) :
    inputHom k i = scalarHom k (coefficients k i) := by
  ext j
  simp only [inputHom, scalarHom, aeval_X]
  fin_cases i <;>
    simp [polynomials, coefficients, parameterHom, PhysicalTorusMorphism.xUnit,
      PhysicalTorusMorphism.yUnit, PhysicalTorusMorphism.evaluation_coordinate,
      coordinateUnit, coordinate]

theorem inputMorphism_eq_scalarMorphism (i : Fin 3) :
    inputMorphism k i = scalarMorphism k (coefficients k i) := by
  unfold inputMorphism scalarMorphism
  rw [inputHom_eq_scalarHom]

/-- One-variable source observables, before forming the relative family. -/
structure LineGeometry (LineObj : Type v) where
  LisseOnUnits : LineObj → Prop
  rank : LineObj → ℕ
  Pure : LineObj → ℝ → Prop
  TameZero : LineObj → Prop
  BreaksLE : LineObj → ℚ → Prop
  Isoclinic : LineObj → ℚ → Prop

variable {k} {Input : Type v} {Point : Type w} {LineObj : Type z}
  {D : CurveData Input Point}

/-- These laws quantify over every parameter-ring unit and every source
object. Multiplication by such a unit is a relative curve automorphism,
fixing the zero and infinity sections. They contain no selected recipe. -/
structure ScalarPullbackRules (F : PullbackData k LineObj Input)
    (L : LineGeometry LineObj) (D : CurveData Input Point) : Prop where
  lisse : ∀ c A, L.LisseOnUnits A → D.Lisse (F.pullback (scalarMorphism k c) A)
  rank : ∀ c A, L.LisseOnUnits A → D.rank (F.pullback (scalarMorphism k c) A) = L.rank A
  pure : ∀ c A t, L.Pure A t → D.Pure (F.pullback (scalarMorphism k c) A) t
  tame : ∀ c A, L.TameZero A → D.TameZero (F.pullback (scalarMorphism k c) A)
  breaks : ∀ c A s, L.BreaksLE A s → D.BreaksLE (F.pullback (scalarMorphism k c) A) s
  isoclinic : ∀ c A s, L.Isoclinic A s → D.Isoclinic (F.pullback (scalarMorphism k c) A) s

/-- Published normalized rank-three Kloosterman source properties. -/
structure Kl3Properties (L : LineGeometry LineObj) (A : LineObj) : Prop where
  lisse : L.LisseOnUnits A
  rank : L.rank A = 3
  pure : L.Pure A 0
  tame : L.TameZero A
  breaks : L.BreaksLE A (1 / 3)

/-- Published nontrivial Artin--Schreier source properties. -/
structure ASProperties (L : LineGeometry LineObj) (A : LineObj) : Prop where
  lisse : L.LisseOnUnits A
  rank : L.rank A = 1
  pure : L.Pure A 0
  tame : L.TameZero A
  slope : L.Isoclinic A 1

variable (F : PullbackData k LineObj Input) (L : LineGeometry LineObj)
  (R : ScalarPullbackRules F L D) (kl as : LineObj)
  (hkl : Kl3Properties L kl) (has : ASProperties L as)

/-- Choose the existing generic construction's inputs to be the literal
recipe. Properties of the relative family are derived from source laws. -/
def canonicalInput : KloostermanInputData D := by
  have hl (i : Fin 3) (A : LineObj) (h : L.LisseOnUnits A) :
      D.Lisse (F.pullback (inputMorphism k i) A) := by
    rw [inputMorphism_eq_scalarMorphism]; exact R.lisse _ _ h
  have hr (i : Fin 3) (A : LineObj) (h : L.LisseOnUnits A) :
      D.rank (F.pullback (inputMorphism k i) A) = L.rank A := by
    rw [inputMorphism_eq_scalarMorphism]; exact R.rank _ _ h
  have hp (i : Fin 3) (A : LineObj) (h : L.Pure A 0) :
      D.Pure (F.pullback (inputMorphism k i) A) 0 := by
    rw [inputMorphism_eq_scalarMorphism]; exact R.pure _ _ _ h
  have ht (i : Fin 3) (A : LineObj) (h : L.TameZero A) :
      D.TameZero (F.pullback (inputMorphism k i) A) := by
    rw [inputMorphism_eq_scalarMorphism]; exact R.tame _ _ h
  have hb (i : Fin 3) : D.BreaksLE (F.pullback (inputMorphism k i) kl) (1 / 3) := by
    rw [inputMorphism_eq_scalarMorphism]; exact R.breaks _ _ _ hkl.breaks
  have hs : D.Isoclinic (F.pullback (inputMorphism k 2) as) 1 := by
    rw [inputMorphism_eq_scalarMorphism]; exact R.isoclinic _ _ _ has.slope
  exact {
    first := inputs F kl as 0
    second := inputs F kl as 1
    additive := inputs F kl as 2
    first_lisse := hl 0 kl hkl.lisse
    second_lisse := hl 1 kl hkl.lisse
    additive_lisse := hl 2 as has.lisse
    first_rank := (hr 0 kl hkl.lisse).trans hkl.rank
    second_rank := (hr 1 kl hkl.lisse).trans hkl.rank
    additive_rank := (hr 2 as has.lisse).trans has.rank
    first_pure := hp 0 kl hkl.pure
    second_pure := hp 1 kl hkl.pure
    additive_pure := hp 2 as has.pure
    first_tame := ht 0 kl hkl.tame
    second_tame := ht 1 kl hkl.tame
    additive_tame := ht 2 as has.tame
    first_breaks := hb 0
    second_breaks := hb 1
    additive_slope := hs }

section FiniteField

variable {p : ℕ} [Fact p.Prime]
  (F : PullbackData (ZMod p) LineObj Input) (R : ScalarPullbackRules F L D)

/-- The formerly external recipe identification is now proved. -/
theorem canonicalInput_identifies :
    IdentifiesInputs (canonicalInput F L R kl as hkl has) F kl as :=
  ⟨rfl, rfl, rfl⟩

variable {C : Type a} [Category.{b} C] [Abelian C] [MonoidalCategory C]
  {H : CohomologyData Input C} {P : ParameterData C}
  {Obj : Type u} {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : PublishedSupportRules.RationalStalkRealization p SD}

/-- The original physical construction evaluated at the canonical inputs,
with neither an input-identification premise nor individual input bounds. -/
theorem canonical_physical_complexity
    (CR : CurveRules D) (G : CohomologyRules D H P)
    (O : TorusOperationData p C) (T : TorusArithmeticData p C) (TR : TorusRules P O T)
    (IC : IntermediateExtensionData realization C)
    (f : ℕ → ℕ) (h unitCap : ℕ) (ci : Input → ℕ) (cp : C → ℕ)
    (cm : TorusMorphismComplexity (ZMod p))
    (Q : OperationBounds (D := D) (H := H) (P := P) f unitCap ci cp cm O IC)
    (QM : TorusPolynomialRules cm)
    (S : PrimitiveClasses LineObj) (cl : LineObj → ℕ)
    (cs : MorphismComplexity (ZMod p))
    (QS : Bounds F S f h cl ci cs) (QSM : PolynomialRules (ZMod p) cs)
    (hhyper : S.Hypergeometric kl 3) (hAS : S.NontrivialArtinSchreier as)
    (α m m' n n' : (ZMod p)ˣ) (I : Finset (Fin 4)) :
    SD.complexity (physicalObjects IC
      (entryObjects (H := H) (P := P) (canonicalInput F L R kl as hkl has) O α m m' n n') I) ≤
      physicalCap f (sourceCap f h) unitCap :=
  physical_complexity_of_source_recipe (canonicalInput F L R kl as hkl has)
    CR G O T TR IC f h unitCap ci cp cm Q QM F S cl cs QS QSM kl as hhyper hAS
    (canonicalInput_identifies (F := F) (L := L) (R := R)
      (kl := kl) (as := as) hkl has) α m m' n n' I

end FiniteField
end PrimeGap182.TypeIII.CanonicalCurveInput

#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.parameterHom_xUnit
#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.parameterHom_yUnit
#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.inputHom_eq_scalarHom
#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.inputMorphism_eq_scalarMorphism
#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.canonicalInput
#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.canonicalInput_identifies
#print axioms PrimeGap182.TypeIII.CanonicalCurveInput.canonical_physical_complexity
