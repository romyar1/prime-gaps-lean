import TypeIIIQSTPrimitiveBridgesFromCommonKatzConstruction
import TypeIIIQSTDualityBridgesFromSmoothLisseVerdier
import TypeIIILinePurityFromStalks

/-!
# Whole-source lissity from the same genuine Katz pullbacks

The three actual maps x, lambda*x, xi*x on Gm^3 factor through the SAME
ordinary Gm inclusion into A1, proved by their coordinate units. General
unequal-length Katz lissity, ordinary zero-extension restriction and SAME-U
lissity closure then apply to the normalized Kl3 source factors and tensor.
These general laws are fixed before the field/character; no selected source
lissity, numerical estimate, or completed scalar/curve rules are premises.
Genuine continuous-adic realization of these laws remains external.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.SourceGlobalLissityFromKatzPullbacks
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction

variable (K : Type) [Field K]

/-- The three source functions are actual units of the coordinate ring. -/
def inputUnit (i : Fin 3) : (StartingSourceMaps.SourceRing K)ˣ :=
  ![StartingSourceMaps.coordinateUnit K 0,
    StartingSourceMaps.coordinateUnit K 1 * StartingSourceMaps.coordinateUnit K 0,
    StartingSourceMaps.coordinateUnit K 2 * StartingSourceMaps.coordinateUnit K 0] i

theorem inputUnit_val (i : Fin 3) :
    (inputUnit K i : StartingSourceMaps.SourceRing K) =
      StartingSourceMaps.inputHom K i (X 0) := by
  fin_cases i <;> simp [inputUnit, StartingSourceMaps.inputHom,
    StartingSourceMaps.polynomials, StartingSourceMaps.coordinateUnit,
    StartingSourceMaps.coordinate]

/-- Literal Laurent-coordinate factor of each original source map. -/
def inputGmHom (i : Fin 3) : LaurentPolynomial K →ₐ[K] StartingSourceMaps.SourceRing K where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap K _) (inputUnit K i)
  commutes' c := by
    change LaurentPolynomial.eval₂ (algebraMap K _) (inputUnit K i)
      (LaurentPolynomial.C ((algebraMap K K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    simp

theorem inputGmHom_comp_inclusion (i : Fin 3) :
    (inputGmHom K i).comp (ArithmeticSourceMaps.localInputHom K K) =
      StartingSourceMaps.inputHom K i := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  simp only [AlgHom.comp_apply, ArithmeticSourceMaps.localInputHom, aeval_X]
  change LaurentPolynomial.eval₂ (algebraMap K _) (inputUnit K i)
      (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  exact inputUnit_val K i

def inputGmMorphism (i : Fin 3) :
    StartingSourceMaps.sourceScheme K ⟶ ArithmeticSourceMaps.fiberScheme K :=
  Spec.map (CommRingCat.ofHom (inputGmHom K i).toRingHom)

/-- Factorization of genuine schemes, independent of their finite-field points. -/
theorem inputMorphism_factors (i : Fin 3) :
    inputGmMorphism K i ≫ ArithmeticSourceMaps.localInputMorphism K K =
      StartingSourceMaps.inputMorphism K i := by
  dsimp only [inputGmMorphism, ArithmeticSourceMaps.localInputMorphism,
    StartingSourceMaps.inputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (inputGmHom_comp_inclusion K i))

/-- Every parameter-ring unit defines a genuine unit scalar on Gm^3. -/
def scalarInputUnit (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    (StartingSourceMaps.SourceRing K)ˣ :=
  Units.map (CanonicalCurveInput.parameterHom K).toRingHom c *
    StartingSourceMaps.coordinateUnit K 0

def scalarGmHom (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    LaurentPolynomial K →ₐ[K] StartingSourceMaps.SourceRing K where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap K _) (scalarInputUnit K c)
  commutes' a := by
    change LaurentPolynomial.eval₂ (algebraMap K _) (scalarInputUnit K c)
      (LaurentPolynomial.C ((algebraMap K K) a)) = _
    rw [LaurentPolynomial.eval₂_C]
    simp

theorem scalarGmHom_comp_inclusion (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    (scalarGmHom K c).comp (ArithmeticSourceMaps.localInputHom K K) =
      CanonicalCurveInput.scalarHom K c := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  simp only [AlgHom.comp_apply, ArithmeticSourceMaps.localInputHom, aeval_X]
  change LaurentPolynomial.eval₂ (algebraMap K _) (scalarInputUnit K c)
      (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  simp only [CanonicalCurveInput.scalarHom, aeval_X]
  rfl

def scalarGmMorphism (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    StartingSourceMaps.sourceScheme K ⟶ ArithmeticSourceMaps.fiberScheme K :=
  Spec.map (CommRingCat.ofHom (scalarGmHom K c).toRingHom)

/-- ALL original scalar maps factor through the SAME Gm inclusion. -/
theorem scalarMorphism_factors (c : (PhysicalTorusMorphism.TorusRing K)ˣ) :
    scalarGmMorphism K c ≫ ArithmeticSourceMaps.localInputMorphism K K =
      CanonicalCurveInput.scalarMorphism K c := by
  dsimp only [scalarGmMorphism, ArithmeticSourceMaps.localInputMorphism,
    CanonicalCurveInput.scalarMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (scalarGmHom_comp_inclusion K c))

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y),
    L Y A → L X ((U.pull f).obj A))

/-- SAME-U composition applied to the proved global coordinate square. -/
def sourceRestrictionIso (i : Fin 3) (A : C (StartingSourceMaps.affineLine K)) :
    (U.pull (StartingSourceMaps.inputMorphism K i)).obj A ≅
      (U.pull (inputGmMorphism K i)).obj
        ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A) :=
  eqToIso (congrArg (fun f => (U.pull f).obj A) (inputMorphism_factors K i).symm) ≪≫
    ((U.composition (inputGmMorphism K i) (ArithmeticSourceMaps.localInputMorphism K K)).app A).symm

include lissePull in
/-- ALL original source factors are globally lisse when the restriction is. -/
theorem sourceFactor_lisse (i : Fin 3) (A : C (StartingSourceMaps.affineLine K))
    (hA : L (ArithmeticSourceMaps.fiberScheme K)
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)) :
    L (StartingSourceMaps.sourceScheme K)
      ((U.pull (StartingSourceMaps.inputMorphism K i)).obj A) := by
  exact (L _).prop_of_iso (sourceRestrictionIso K C U i A).symm
    (lissePull _ _ hA)

def lineLisseOnUnits (A : C (StartingSourceMaps.affineLine K)) : Prop :=
  L (ArithmeticSourceMaps.fiberScheme K)
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)

/-- The line guard is actual global lissity of SAME-U restriction. All four
original numeric/local observable fields are preserved without modification. -/
def bindLineLisseOnUnits (observables : LinePurityFromStalks.Observables
    (C (StartingSourceMaps.affineLine K))) :
    LinePurityFromStalks.Observables (C (StartingSourceMaps.affineLine K)) where
  LisseOnUnits := lineLisseOnUnits K C U L
  rank := observables.rank
  TameZero := observables.TameZero
  BreaksLE := observables.BreaksLE
  Isoclinic := observables.Isoclinic

def scalarRestrictionIso (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K)) :
    (U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A ≅
      (U.pull (scalarGmMorphism K c)).obj
        ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A) :=
  eqToIso (congrArg (fun f => (U.pull f).obj A) (scalarMorphism_factors K c).symm) ≪≫
    ((U.composition (scalarGmMorphism K c) (ArithmeticSourceMaps.localInputMorphism K K)).app A).symm

include lissePull in
/-- Exact ALL-parameter-unit scalar lissity rule under the actual line guard. -/
theorem scalar_lisse (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K)) (hA : lineLisseOnUnits K C U L A) :
    L (StartingSourceMaps.sourceScheme K)
      ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) :=
  (L _).prop_of_iso (scalarRestrictionIso K C U c A).symm (lissePull _ _ hA)

variable (O : Constructions C)
  (zeroRestriction : ∀ (E : Type) [Field E] (h2 : (2 : E) ≠ 0),
    O.zero E h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism E E) ≅
      𝟭 (C (ArithmeticSourceMaps.fiberScheme E)))
  (unequalKatzLisse : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (a : KatzIndex E), a.upper.length ≠ a.lower.length →
      L (ArithmeticSourceMaps.fiberScheme E) (member C O E h2 a))

variable [Fintype K] (h2 : (2 : K) ≠ 0)

/-- The normalized SAME Kl3 restricts to its actual Tate-one Katz member. -/
def normalizedKlRestrictionIso (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    (U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj
      ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) ≅
      member C O K h2 (kloostermanIndex ψ hψ 3 (by decide) 1) :=
  (U.pull (ArithmeticSourceMaps.localInputMorphism K K)).mapIso
    ((O.zeroTate K h2 1).app
      (O.katz K h2 (kloostermanIndex ψ hψ 3 (by decide) 0))).symm ≪≫
    (zeroRestriction K h2).app _

include zeroRestriction unequalKatzLisse in
/-- Published unequal-length lissity applies to rank-three Kl for EVERY ψ. -/
theorem normalizedKl_restriction_lisse (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    L (ArithmeticSourceMaps.fiberScheme K)
      ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj
        ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ))) := by
  apply (L _).prop_of_iso (normalizedKlRestrictionIso K C U O zeroRestriction h2 ψ hψ).symm
  exact unequalKatzLisse K h2 (kloostermanIndex ψ hψ 3 (by decide) 1)
    (by simp [kloostermanIndex])

include lissePull zeroRestriction unequalKatzLisse in
theorem normalizedKl_sourceFactor_lisse (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1)
    (i : Fin 3) :
    L (StartingSourceMaps.sourceScheme K)
      ((U.pull (StartingSourceMaps.inputMorphism K i)).obj
        ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ))) :=
  sourceFactor_lisse K C U L lissePull i _
    (normalizedKl_restriction_lisse K C U L O zeroRestriction unequalKatzLisse h2 ψ hψ)

variable [∀ X, MonoidalCategory (C X)]
  (lisseTensor : ∀ (X : Scheme) (A B : C X), L X A → L X B → L X (A ⊗ B))

variable [∀ X, MonoidalClosed (C X)]
  (lisseDual : ∀ (X : Scheme) (V : C X), L X V →
    L X ((QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C X).obj (Opposite.op V)))
  (standardASLisse : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
    (ψ : AddChar E (PadicAlgCl 2)), ψ ≠ 1 →
      L (StartingSourceMaps.affineLine E) (O.artinSchreier E h2 ψ))

/-- Exact source recipe: (Kl(x) tensor dual Kl(lambda*x)) tensor AS(xi*x). -/
def sourceInput (kl as : C (StartingSourceMaps.affineLine K)) : C (StartingSourceMaps.sourceScheme K) :=
  ((U.pull (StartingSourceMaps.inputMorphism K 0)).obj kl ⊗
    (QSTDualityBridgesFromSmoothLisseVerdier.ordinaryDual C _).obj
      (Opposite.op ((U.pull (StartingSourceMaps.inputMorphism K 1)).obj kl))) ⊗
        (U.pull (StartingSourceMaps.inputMorphism K 2)).obj as

include lissePull lisseTensor zeroRestriction unequalKatzLisse lisseDual standardASLisse in
/-- Whole-source lissity of the literal normalized Kl3/AS input recipe. -/
theorem normalizedKlAS_sourceInput_lisse (ψ : AddChar K (PadicAlgCl 2)) (hψ : ψ ≠ 1) :
    L (StartingSourceMaps.sourceScheme K)
      (sourceInput K C U ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ))
        (O.artinSchreier K h2 ψ)) := by
  apply lisseTensor
  · apply lisseTensor
    · exact normalizedKl_sourceFactor_lisse K C U L lissePull O zeroRestriction unequalKatzLisse h2 ψ hψ 0
    · exact lisseDual _ _ (normalizedKl_sourceFactor_lisse K C U L lissePull O zeroRestriction unequalKatzLisse h2 ψ hψ 1)
  · exact lissePull _ _ (standardASLisse K h2 ψ hψ)

end PrimeGap182.TypeIII.SourceGlobalLissityFromKatzPullbacks
