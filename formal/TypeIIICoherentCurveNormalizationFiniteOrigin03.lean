import TypeIIIPublishedLocalConstruction
import TypeIIICanonicalCurveInput
import TypeIIIFourierSourcePullbacks

/-!
# GENERAL curve normalization and the actual eligible local correlation

Ambient ordinary source pullbacks are retained. The SAME standard ordinary
j-star operation is followed by the ONE standard normalization
N(A) = perverseH0(A[1]). The finite-origin data/rules are computed by
precomposing the genuine GENERAL perverse finite-origin operation with N.
No all-ordinary finite-origin theorem is assumed.

The actual local Kl correlation is derived lisse with breaks <=1/3 from
primitive source properties and GENERAL guarded scalar/tensor/dual rules.
The GENERAL no-point-sections criterion makes its ordinary j-star[1]
perverse, and GENERAL perverse truncation supplies its normalization iso.
No selected correlation lissity/perversity, small-slope conclusion, family
middle iso, rank-six, Fu phase profile or Type III bound is an input.

All predicates/operators and theorem projections below must be the SAME
genuine standard constructible adic theory. This does not construct that
theory or infer published meaning from arbitrary predicates. The actual
Fourier/normalization/infinity restriction diagrams are not proved here.
No current Lean execution or historical PASS is claimed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03

open CanonicalLocalCorrelation CanonicalCurveInput FourierSourcePullbacks
open GenericSourceSpecialization PublishedPhysicalConstruction PublishedPhaseApplication
open PublishedLocalConstruction

universe u v w z a b c d e f g h i j k l

section Reindexing
variable {K : Type u} [Field K] {E : Type v} [Field E]
  {I : Type w} [Group I] {Outer : Type z} [Group Outer]
  {Ord : Type a} [Category.{b} Ord]
  {Perv : Type c} [Category.{d} Perv]
  {LF : PublishedLocalConstruction.LocalFourierData K E I Outer}

/-- The standard perverse operation is evaluated on N(A), never directly
on an arbitrary ordinary A. All maps are the same original perverse maps. -/
def normalizedFiniteOriginData (N : Ord ⥤ Perv) (FO : PublishedLocalConstruction.FiniteOriginData Perv LF) :
    PublishedLocalConstruction.FiniteOriginData Ord LF where
  infinity A := FO.infinity (N.obj A)
  infinity_admissible A := FO.infinity_admissible (N.obj A)
  origin s hs A := FO.origin s hs (N.obj A)
  boundary s hs A := FO.boundary s hs (N.obj A)
  toVanishing s hs A := FO.toVanishing s hs (N.obj A)
  toBoundary s hs A := FO.toBoundary s hs (N.obj A)

/-- The only finite-origin theorem premise is the genuine GENERAL law on
perverse objects. Its all-ordinary reindexing is computed, not assumed. -/
theorem normalizedFiniteOriginRules
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : Ord ⥤ Perv) (FO : PublishedLocalConstruction.FiniteOriginData Perv LF)
    (publishedRules : PublishedLocalConstruction.FiniteOriginRules p FO) :
    PublishedLocalConstruction.FiniteOriginRules p (normalizedFiniteOriginData N FO) where
  exact hp s hs A := publishedRules.exact hp s hs (N.obj A)
  constant hp s hs A := publishedRules.constant hp s hs (N.obj A)

end Reindexing

section EligibleCorrelation
variable {K : Type u} [Field K]
  {L : Type v} [Category.{w} L] [MonoidalCategory L]
  {Ord : Type z} [Category.{a} Ord]
  {Derived : Type b} [Category.{c} Derived]
  {Perv : Type d} [Category.{e} Perv]
  (ops : SheafOperations (PhaseField K) L Ord)
  (lisse : L → Prop) (breaksLE : L → ℚ → Prop)
  (scalarLisse : ∀ lambda A, lisse A → lisse ((ops.scalar lambda).obj A))
  (dualLisse : ∀ A, lisse A → lisse (ops.dual A))
  (tensorLisse : ∀ A B, lisse A → lisse B → lisse (A ⊗ B))
  (scalarBreaks : ∀ lambda A r, breaksLE A r → breaksLE ((ops.scalar lambda).obj A) r)
  (dualBreaks : ∀ A r, breaksLE A r → breaksLE (ops.dual A) r)
  (tensorBreaks : ∀ A B r, breaksLE A r → breaksLE B r → breaksLE (A ⊗ B) r)

include scalarLisse dualLisse tensorLisse scalarBreaks dualBreaks tensorBreaks

/-- GENERAL closure laws derive the local source correlation eligibility;
this lemma holds for every eligible source, unit scalar and break bound. -/
theorem correlation_eligible
    (kl : L) (lambda : (PhaseField K)ˣ) (r : ℚ) (hL : lisse kl) (hB : breaksLE kl r) :
    lisse (CanonicalLocalCorrelation.correlation ops kl lambda) ∧ breaksLE (CanonicalLocalCorrelation.correlation ops kl lambda) r := by
  exact ⟨tensorLisse _ _ hL (dualLisse _ (scalarLisse lambda kl hL)),
    tensorBreaks _ _ r hB (dualBreaks _ r (scalarBreaks lambda kl r hB))⟩

variable (N : Ord ⥤ Perv) (underlying : Perv ⥤ Derived) (shiftOne : Ord ⥤ Derived)
  (isPerverse : Derived → Prop) (noPointSections : Ord → Prop)
  (jstarNoPoint : ∀ A, lisse A → noPointSections (ops.middleExtension.obj A))
  (curveCriterion : ∀ B, noPointSections B → isPerverse (shiftOne.obj B))
  (normalizeAlreadyPerverse : ∀ B, isPerverse (shiftOne.obj B) →
    Nonempty (underlying.obj (N.obj B) ≅ shiftOne.obj B))

include scalarLisse dualLisse tensorLisse scalarBreaks dualBreaks tensorBreaks
  jstarNoPoint curveCriterion normalizeAlreadyPerverse

/-- Apply the GENERAL curve criterion and truncation identity on the SAME
actual j-star correlation. The source primitive facts are the only guards. -/
theorem normalized_correlation_is_actual_shift
    (kl : L) (lambda : (PhaseField K)ˣ) (r : ℚ) (hL : lisse kl) (hB : breaksLE kl r) :
    isPerverse (shiftOne.obj (CanonicalLocalCorrelation.perverseCorrelation ops kl lambda)) ∧
      Nonempty (underlying.obj (N.obj (CanonicalLocalCorrelation.perverseCorrelation ops kl lambda)) ≅
        shiftOne.obj (CanonicalLocalCorrelation.perverseCorrelation ops kl lambda)) := by
  have h := correlation_eligible ops lisse breaksLE scalarLisse dualLisse tensorLisse
    scalarBreaks dualBreaks tensorBreaks kl lambda r hL hB
  have hp := curveCriterion _ (jstarNoPoint _ h.1)
  exact ⟨hp, normalizeAlreadyPerverse _ hp⟩

end EligibleCorrelation

section ActualSource
variable (K : Type u) [Field K]
  {Line : Type v} [Category.{w} Line]
  {Input : Type z} [Category.{a} Input]
  {GenericInput : Type b} [Category.{c} GenericInput]
  {L : Type d} [Category.{e} L] [MonoidalCategory L]
  {Ord : Type f} [Category.{g} Ord]
  (P : PullbackComposition (Line := Line) (Input := Input) (GenericInput := GenericInput) K)
  (R : LocalPullbacks (L := L) K P)
  (dualLocal : L → L) (middle : L ⥤ Ord)
  (LG : LineGeometry Line)
  (lisse : L → Prop) (breaksLE : L → ℚ → Prop)
  (sourceLisse : ∀ A, LG.LisseOnUnits A → lisse (localSource K P R A))
  (sourceBreaks : ∀ A r, LG.BreaksLE A r → breaksLE (localSource K P R A) r)

variable
  (scalarLisse : ∀ lambda A, lisse A → lisse ((((localSheafOperations K P R dualLocal middle)).scalar lambda).obj A))
  (dualLisse : ∀ A, lisse A → lisse (((localSheafOperations K P R dualLocal middle)).dual A))
  (tensorLisse : ∀ A B, lisse A → lisse B → lisse (A ⊗ B))
  (scalarBreaks : ∀ lambda A r, breaksLE A r → breaksLE ((((localSheafOperations K P R dualLocal middle)).scalar lambda).obj A) r)
  (dualBreaks : ∀ A r, breaksLE A r → breaksLE (((localSheafOperations K P R dualLocal middle)).dual A) r)
  (tensorBreaks : ∀ A B r, breaksLE A r → breaksLE B r → breaksLE (A ⊗ B) r)

include P R dualLocal middle LG lisse breaksLE
  sourceLisse sourceBreaks scalarLisse dualLisse tensorLisse
  scalarBreaks dualBreaks tensorBreaks

/-- Published primitive Kl3 properties plus GENERAL restriction/closure
laws derive the actual correlation's lissity and <=1/3 bound. -/
theorem actualSourceCorrelation_eligible
    (kl : Line) (hkl : Kl3Properties LG kl) (lambda : (PhaseField K)ˣ) :
    lisse (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda) ∧
      breaksLE (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda) (1 / 3) := by
  exact correlation_eligible (localSheafOperations K P R dualLocal middle) lisse breaksLE scalarLisse dualLisse tensorLisse
    scalarBreaks dualBreaks tensorBreaks _ lambda (1 / 3)
    (sourceLisse kl hkl.lisse) (sourceBreaks kl (1 / 3) hkl.breaks)

section ActualNormalization

variable {Derived : Type i} [Category.{j} Derived]
  {Perv : Type k} [Category.{l} Perv]
  (N : Ord ⥤ Perv) (underlying : Perv ⥤ Derived) (shiftOne : Ord ⥤ Derived)
  (isPerverse : Derived → Prop) (noPointSections : Ord → Prop)
  (jstarNoPoint : ∀ A, lisse A → noPointSections (((localSheafOperations K P R dualLocal middle)).middleExtension.obj A))
  (curveCriterion : ∀ B, noPointSections B → isPerverse (shiftOne.obj B))
  (normalizeAlreadyPerverse : ∀ B, isPerverse (shiftOne.obj B) →
    Nonempty (underlying.obj (N.obj B) ≅ shiftOne.obj B))

include jstarNoPoint curveCriterion normalizeAlreadyPerverse
/-- The SAME actual ordinary source correlation has the required perverse
shift and normalization iso by GENERAL guarded curve/truncation laws. -/
theorem actualSourceCorrelation_normalization
    (kl : Line) (hkl : Kl3Properties LG kl) (lambda : (PhaseField K)ˣ) :
    isPerverse (shiftOne.obj (CanonicalLocalCorrelation.perverseCorrelation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda)) ∧
      Nonempty (underlying.obj (N.obj
        (CanonicalLocalCorrelation.perverseCorrelation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda)) ≅
        shiftOne.obj (CanonicalLocalCorrelation.perverseCorrelation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda)) := by
  exact normalized_correlation_is_actual_shift (localSheafOperations K P R dualLocal middle) lisse breaksLE
    scalarLisse dualLisse tensorLisse scalarBreaks dualBreaks tensorBreaks
    N underlying shiftOne isPerverse noPointSections jstarNoPoint curveCriterion
    normalizeAlreadyPerverse _ lambda (1 / 3)
    (sourceLisse kl hkl.lisse) (sourceBreaks kl (1 / 3) hkl.breaks)

end ActualNormalization

variable {I : Type h} [Group I]
  (Jinf : L ⥤ FDRep ℂ I)
  (smallPart : FDRep ℂ I → FDRep ℂ I)
  (smallPartRecognition : ∀ A r, breaksLE A r → r < 1 →
    Representation.Equiv (smallPart (Jinf.obj A)).ρ (Jinf.obj A).ρ)

include Jinf smallPart smallPartRecognition

/-- The GENERAL guarded slope-decomposition comparison is applied only
with the actually derived <=1/3 bound. No family small-part iso is assumed. -/
def actualSourceCorrelation_smallPartEquiv
    (kl : Line) (hkl : Kl3Properties LG kl) (lambda : (PhaseField K)ˣ) :
    Representation.Equiv
      (smallPart (Jinf.obj (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda))).ρ
      (Jinf.obj (CanonicalLocalCorrelation.correlation (localSheafOperations K P R dualLocal middle) (localSource K P R kl) lambda)).ρ :=
  smallPartRecognition _ (1 / 3)
    (actualSourceCorrelation_eligible K P R dualLocal middle LG lisse breaksLE
      sourceLisse sourceBreaks scalarLisse dualLisse tensorLisse scalarBreaks dualBreaks
      tensorBreaks kl hkl lambda).2 (by norm_num)

end ActualSource

end PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03

#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.normalizedFiniteOriginData
#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.normalizedFiniteOriginRules
#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.correlation_eligible
#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.normalized_correlation_is_actual_shift
#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.actualSourceCorrelation_eligible
#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.actualSourceCorrelation_normalization
#print axioms PrimeGap182.TypeIII.CoherentCurveNormalizationFiniteOrigin03.actualSourceCorrelation_smallPartEquiv
