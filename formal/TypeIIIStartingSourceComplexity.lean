import TypeIIIStartingSourceMaps

/-!
# Complexity of the explicit Kl3/Artin--Schreier input recipe

Start with the zero extension of the normalized Kl3 sheaf to A1 and the
nontrivial Artin--Schreier sheaf on A1, with the standard embedding in P1.
QST 7.8(1), 7.5(1), and 6.8 supply the general class and pullback bounds
below. Pull back along the actual maps proved in StartingSourceMaps.

This derives the three input bounds and feeds the existing physical
construction theorem. It leaves the identification with the existing
KloostermanInputData explicit; constructing compatible sheaf realizations
and proving that identification are not accomplished by this adapter.
Source: https://arxiv.org/html/2101.00635v4.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Classical MonoidalCategory
namespace PrimeGap182.TypeIII.StartingSourceComplexity

open PublishedPhysicalConstruction PublishedConstructionComplexity
open PublishedPolynomialComplexity PublishedUniformComplexity StartingSourceMaps

universe u v w z a b

variable {k : Type u} [Field k] {Input : Type v} {LineObj : Type w}

/-- Pullback from the affine line to the parameterized curve Gm^3. -/
structure PullbackData (k : Type u) [Field k] (LineObj : Type w) (Input : Type v) where
  pullback : (sourceScheme k ⟶ affineLine k) → LineObj → Input

def inputs (F : PullbackData k LineObj Input) (kl as : LineObj) : Fin 3 → Input :=
  ![F.pullback (inputMorphism k 0) kl,
    F.pullback (inputMorphism k 1) kl,
    F.pullback (inputMorphism k 2) as]

/-- The predicates refer to the published sheaf classes, not arbitrary
rank-three or rank-one objects. The normalized Kl3 twist changes no
geometric complexity. Extension by zero to A1 preserves the P1 complexity. -/
structure PrimitiveClasses (LineObj : Type w) where
  Hypergeometric : LineObj → ℕ → Prop
  NontrivialArtinSchreier : LineObj → Prop

/-- General results for every object in the respective classes and every
map between these fixed embedded spaces. Common f and h are chosen before
the characteristic and the additive character. -/
structure Bounds (F : PullbackData k LineObj Input) (S : PrimitiveClasses LineObj)
    (f : ℕ → ℕ) (h : ℕ) (cl : LineObj → ℕ) (ci : Input → ℕ)
    (cm : MorphismComplexity k) : Prop where
  hypergeometric : ∀ A r, S.Hypergeometric A r → cl A ≤ h * r
  artinSchreier : ∀ A, S.NontrivialArtinSchreier A → cl A ≤ 1
  pullback : ∀ g A, ci (F.pullback g A) ≤ f (max (cm g) (cl A))

def sourceCap (f : ℕ → ℕ) (h : ℕ) : ℕ :=
  envelope f (max 1870768416 (max (h * 3) 1))

variable (F : PullbackData k LineObj Input) (S : PrimitiveClasses LineObj)
  (f : ℕ → ℕ) (h : ℕ) (cl : LineObj → ℕ) (ci : Input → ℕ)
  (cm : MorphismComplexity k) (Q : Bounds F S f h cl ci cm)
  (QM : PolynomialRules k cm) (kl as : LineObj)
  (hkl : S.Hypergeometric kl 3) (has : S.NontrivialArtinSchreier as)

include Q QM in
theorem pullback_complexity_le (A : LineObj) (i : Fin 3)
    (hA : cl A ≤ max (h * 3) 1) :
    ci (F.pullback (inputMorphism k i) A) ≤ sourceCap f h := by
  apply (Q.pullback _ _).trans
  exact le_envelope f (max_le_max (input_morphism_complexity_le k QM i) hA)

include Q QM hkl has in
/-- All three actual pullbacks have the same characteristic-independent
cap; their individual complexities are conclusions, not supplied premises. -/
theorem inputs_complexity_le (i : Fin 3) :
    ci (inputs F kl as i) ≤ sourceCap f h := by
  have hk : cl kl ≤ max (h * 3) 1 := (Q.hypergeometric kl 3 hkl).trans (le_max_left _ _)
  have ha : cl as ≤ max (h * 3) 1 := (Q.artinSchreier as has).trans (le_max_right _ _)
  fin_cases i
  · exact pullback_complexity_le F S f h cl ci cm Q QM kl 0 hk
  · exact pullback_complexity_le F S f h cl ci cm Q QM kl 1 hk
  · exact pullback_complexity_le F S f h cl ci cm Q QM as 2 ha

section ExistingConstruction

variable {p : ℕ} [Fact p.Prime]
  {CurveInput : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData CurveInput Point} {H : CohomologyData CurveInput C} {P : ParameterData C}
  {Obj : Type a} {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : PublishedSupportRules.RationalStalkRealization p SD}
  {L : Type b}

/-- Still a family-identification obligation: the already-used geometric
inputs must be these pullbacks of the same two primitive sheaves. -/
structure IdentifiesInputs (K : KloostermanInputData D)
    (F : PullbackData (ZMod p) L CurveInput) (kl as : L) : Prop where
  first : K.first = inputs F kl as 0
  second : K.second = inputs F kl as 1
  additive : K.additive = inputs F kl as 2

/-- The literal existing physical family is bounded from the two primitive
class results and the stated recipe identification. No cap on its initial
three curve objects or its final IC objects is assumed. -/
theorem physical_complexity_of_source_recipe
    (K : KloostermanInputData D) (R : CurveRules D) (G : CohomologyRules D H P)
    (O : TorusOperationData p C) (T : TorusArithmeticData p C) (TR : TorusRules P O T)
    (IC : IntermediateExtensionData realization C)
    (f : ℕ → ℕ) (h unitCap : ℕ) (ci : CurveInput → ℕ) (cp : C → ℕ)
    (cm : TorusMorphismComplexity (ZMod p))
    (Q : OperationBounds (D := D) (H := H) (P := P) f unitCap ci cp cm O IC)
    (QM : TorusPolynomialRules cm)
    (F : PullbackData (ZMod p) L CurveInput) (S : PrimitiveClasses L)
    (cl : L → ℕ) (cs : MorphismComplexity (ZMod p))
    (QS : Bounds F S f h cl ci cs) (QSM : PolynomialRules (ZMod p) cs)
    (kl as : L) (hkl : S.Hypergeometric kl 3) (has : S.NontrivialArtinSchreier as)
    (J : IdentifiesInputs K F kl as)
    (α m m' n n' : (ZMod p)ˣ) (I : Finset (Fin 4)) :
    SD.complexity (physicalObjects IC
      (entryObjects (H := H) (P := P) K O α m m' n n') I) ≤
      physicalCap f (sourceCap f h) unitCap := by
  have hb := inputs_complexity_le F S f h cl ci cs QS QSM kl as hkl has
  exact physical_objects_complexity_le K R G O T TR IC f (sourceCap f h) unitCap
    ci cp cm Q QM
    (by simpa only [J.first] using hb 0)
    (by simpa only [J.second] using hb 1)
    (by simpa only [J.additive] using hb 2) α m m' n n' I

end ExistingConstruction
end PrimeGap182.TypeIII.StartingSourceComplexity

#print axioms PrimeGap182.TypeIII.StartingSourceComplexity.pullback_complexity_le
#print axioms PrimeGap182.TypeIII.StartingSourceComplexity.inputs_complexity_le
#print axioms PrimeGap182.TypeIII.StartingSourceComplexity.physical_complexity_of_source_recipe
