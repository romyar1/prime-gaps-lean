import TypeIIIPrimitiveTracesFromGeneralKatzArtinSchreierFormulas
import TypeIIIPrimitiveTateTraceFromGeneralStalkNormalization
import TypeIIIPrimitiveLinePropertiesFromGlobalLissity
import TypeIIIQSTHypergeometricRankFromGeneralKatzRank
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Analysis.Complex.Basic

/-!
# Primitive ranks and weights from the SAME general Katz construction

The raw weight theorem covers ALL finite base fields, ALL nontrivial additive
characters and ALL positive Kloosterman ranks. It is stated on coefficient
characteristic roots of the SAME untwisted Katz object. Actual scalar extension
and Frobenius conjugacy transport those roots to the existing complex fiber.
ALL integer point Tate operations transport weight by minus twice the twist.
The AS weight zero is derived from its general rank-one Frobenius description
and the finite order of every additive-character value, without a new purity
dictionary. The primitive Kl3 branch retains its nontrivial-character guard.

Rank uses the already general Katz/generic-Tate rank theorems. The arbitrary
line rank observable is bound by an explicit ALL-lisse generic-rank dictionary;
the SAME geometric and arithmetic fibers are bound by an ALL-lisse generic to
finite-point rank comparison. Neither dictionary is inferred from exact U.
All continuous finite-coefficient/adic and physical model matching is external.
Primary source: Katz GKM Theorem4.1.1(1), printed49, and section4.3, printed59-60.
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical TensorProduct

namespace PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber PrimitiveTracesFromGeneralKatzArtinSchreierFormulas
open QSTGenericFiberFromActualGenericPoint QSTHypergeometricRankFromGeneralKatzRank
open TwoAdicComplexEmbedding
open scoped TwoAdicComplexEmbedding

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (F : ArithmeticFibers C) (O : Constructions C) (B : CoefficientFibers C F)

instance arithmeticFinite (E : Type) [Field E] [Fintype E] (A : C (Spec (.of E))) :
    FiniteDimensional ℂ ((F.fiber E).obj A) := F.finite E A

instance coefficientFinite (E : Type) [Field E] [Fintype E] (A : C (Spec (.of E))) :
    FiniteDimensional Coefficient ((B.fiber E).obj A) := B.finite E A

instance extendedCoefficientFinite (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) :
    FiniteDimensional ℂ ((B.fiber E ⋙ ModuleCat.extendScalars complexEquiv.toRingHom).obj A) := by
  let _ : Algebra Coefficient ℂ := complexEquiv.toRingHom.toAlgebra
  change Module.Finite ℂ (ℂ ⊗[Coefficient] ((B.fiber E).obj A))
  infer_instance

instance extendedCoefficientFiniteDirect (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) :
    FiniteDimensional ℂ ((ModuleCat.extendScalars complexEquiv.toRingHom).obj ((B.fiber E).obj A)) :=
  extendedCoefficientFinite C F B E A

def coefficientRoots (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) : Multiset Coefficient := by
  let := B.finite E A
  exact (LinearMap.charpoly ((B.frobenius E).app A).hom).roots

def complexRoots (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) : Multiset ℂ := by
  let := F.finite E A
  exact (LinearMap.charpoly ((F.frobenius E).app A).hom).roots

omit [∀ X, Abelian (C X)] in
include B in
/-- ALL-object characteristic-polynomial transport by actual scalar extension. -/
theorem complex_charpoly (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) :
    LinearMap.charpoly ((F.frobenius E).app A).hom =
      (LinearMap.charpoly ((B.frobenius E).app A).hom).map complexEquiv.toRingHom := by
  let := B.finite E A
  let := F.finite E A
  let e := ((B.complexComparison E).app A).toLinearEquiv
  have h := (e.charpoly_conj ((F.frobenius E).app A).hom).symm
  have ht := congrArg LinearMap.charpoly (B.complexFrobenius E A)
  have hb : LinearMap.charpoly
      ((ModuleCat.extendScalars complexEquiv.toRingHom).map ((B.frobenius E).app A)).hom =
      (LinearMap.charpoly ((B.frobenius E).app A).hom).map complexEquiv.toRingHom := by
    let : FiniteDimensional ℂ ((ModuleCat.extendScalars complexEquiv.toRingHom).obj ((B.fiber E).obj A)) :=
      extendedCoefficientFinite C F B E A
    let _ : Algebra Coefficient ℂ := complexEquiv.toRingHom.toAlgebra
    change LinearMap.charpoly (((B.frobenius E).app A).hom.baseChange ℂ) = _
    exact LinearMap.charpoly_baseChange _ ℂ
  exact h.trans (ht.trans hb)

omit [∀ X, Abelian (C X)] in
include B in
/-- Actual characteristic roots, with multiplicities, on EVERY coefficient object. -/
theorem complex_roots (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) :
    complexRoots C F E A = (coefficientRoots C F B E A).map complexEquiv := by
  let := B.finite E A
  let := F.finite E A
  change (LinearMap.charpoly ((F.frobenius E).app A).hom).roots = _
  rw [complex_charpoly C F B E A]
  exact (IsAlgClosed.splits _).roots_map complexEquiv.toRingHom

omit [∀ X, Abelian (C X)] in
include B in
/-- The SAME finite complex and coefficient fibers have equal dimension. -/
theorem complex_finrank (E : Type) [Field E] [Fintype E]
    (A : C (Spec (.of E))) :
    Module.finrank ℂ ((F.fiber E).obj A) =
      Module.finrank Coefficient ((B.fiber E).obj A) := by
  let := B.finite E A
  let e := ((B.complexComparison E).app A).toLinearEquiv
  refine e.finrank_eq.trans ?_
  let _ : Algebra Coefficient ℂ := complexEquiv.toRingHom.toAlgebra
  change Module.finrank ℂ (ℂ ⊗[Coefficient] ((B.fiber E).obj A)) = _
  exact Module.finrank_baseChange

omit [∀ X, Abelian (C X)] in
/-- Naturality of ONE Frobenius preserves roots across EVERY ordinary iso. -/
theorem complex_roots_iso (E : Type) [Field E] [Fintype E]
    {A D : C (Spec (.of E))} (e : A ≅ D) :
    complexRoots C F E A = complexRoots C F E D := by
  let := F.finite E A
  let := F.finite E D
  let l := ((F.fiber E).mapIso e).toLinearEquiv
  have hnat (v) : l (((F.frobenius E).app A).hom v) =
      ((F.frobenius E).app D).hom (l v) :=
    congrArg (fun m => m.hom v) ((F.frobenius E).naturality e.hom).symm
  have hn : l.conj ((F.frobenius E).app A).hom = ((F.frobenius E).app D).hom := by
    ext v
    change l (((F.frobenius E).app A).hom (l.symm v)) = ((F.frobenius E).app D).hom v
    rw [hnat, l.apply_symm_apply]
  change (LinearMap.charpoly ((F.frobenius E).app A).hom).roots =
    (LinearMap.charpoly ((F.frobenius E).app D).hom).roots
  rw [← hn, l.charpoly_conj]

def pureOnUnits (K : Type) [Field K]
    (A : C (StartingSourceMaps.affineLine K)) (w : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
    ∀ z ∈ complexRoots C F E ((U.pull (RationalPointStalks.linePoint (K := K) (x : E))).obj A),
      Complex.normSq z = (Fintype.card E : ℝ) ^ w

variable
  (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
    O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)
  (rawKloostermanWeight : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
    ∀ z ∈ coefficientRoots C F B E ((U.pull (gmPoint K E x)).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))),
      Complex.normSq (complexEquiv z) = (Fintype.card E : ℝ) ^ (n - 1))

include zeroRestriction rawKloostermanWeight in
/-- EVERY positive raw Katz rank, at every finite-extension unit point. -/
theorem raw_kloosterman_pure (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    pureOnUnits C U F K ((O.zero K h2).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))) (n - 1 : ℕ) := by
  intro E _ _ _ x z hz
  have e := (zeroPointIso C U O zeroRestriction K h2 E x).app
    (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))
  have hi := complex_roots_iso C F E e
  change complexRoots C F E ((U.pull (RationalPointStalks.linePoint (x : E))).obj
    ((O.zero K h2).obj (O.katz K h2 (kloostermanIndex ψ hψ n hn 0)))) =
    complexRoots C F E ((U.pull (gmPoint K E x)).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))) at hi
  rw [hi, complex_roots C F B E] at hz
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hz
  simpa only [Real.rpow_natCast] using rawKloostermanWeight K h2 ψ hψ n hn E x a ha

private theorem root_div_of_smul {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (c : ℂ) (hc : c ≠ 0)
    {z : ℂ} (hz : z ∈ (c • f).charpoly.roots) : z / c ∈ f.charpoly.roots := by
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    (Polynomial.isRoot_of_mem_roots hz)).exists_hasEigenvector
  have he : f v = (z / c) • v := by
    have h := congrArg (fun w => c⁻¹ • w) hv.apply_eq_smul
    simpa only [LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hc, one_smul,
      div_eq_mul_inv, mul_comm c⁻¹ z] using h
  apply (Polynomial.mem_roots f.charpoly_monic.ne_zero).mpr
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨(Module.End.mem_eigenspace_iff).mpr he, hv.2⟩

variable
  (pointTateIso : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ),
    O.lineTate K h2 n ⋙ U.pull x ⋙ F.fiber E ≅ U.pull x ⋙ F.fiber E)
  (pointTateFrobenius : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Fintype E]
    (x : Spec (.of E) ⟶ StartingSourceMaps.affineLine K) (n : ℤ)
    (A : C (StartingSourceMaps.affineLine K)),
    ((pointTateIso K h2 E x n).app A).toLinearEquiv.conj
      ((F.frobenius E).app ((U.pull x).obj ((O.lineTate K h2 n).obj A))).hom =
    (Fintype.card E : ℂ)^(-n) • ((F.frobenius E).app ((U.pull x).obj A)).hom)

include pointTateFrobenius in
/-- ALL ordinary objects and ALL integer twists; actual roots give the weight. -/
theorem tate_pure (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)) (w : ℝ) (n : ℤ)
    (hA : pureOnUnits C U F K A w) :
    pureOnUnits C U F K ((O.lineTate K h2 n).obj A) (w - 2 * n) := by
  intro E _ _ _ x z hz
  let := F.finite E ((U.pull (RationalPointStalks.linePoint (x : E))).obj A)
  let := F.finite E ((U.pull (RationalPointStalks.linePoint (x : E))).obj ((O.lineTate K h2 n).obj A))
  let e := ((pointTateIso K h2 E (RationalPointStalks.linePoint (x : E)) n).app A).toLinearEquiv
  let : FiniteDimensional ℂ ((U.pull (RationalPointStalks.linePoint (x : E)) ⋙ F.fiber E).obj A) :=
    F.finite E _
  let : FiniteDimensional ℂ ((O.lineTate K h2 n ⋙ U.pull (RationalPointStalks.linePoint (x : E)) ⋙ F.fiber E).obj A) :=
    F.finite E _
  let f := ((F.frobenius E).app ((U.pull (RationalPointStalks.linePoint (x : E))).obj A)).hom
  let c : ℂ := (Fintype.card E : ℂ)^(-n)
  have hc : c ≠ 0 := zpow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  have hpoly := congrArg LinearMap.charpoly
    (pointTateFrobenius K h2 E (RationalPointStalks.linePoint (x : E)) n A)
  have hi := e.charpoly_conj
    ((F.frobenius E).app ((U.pull (RationalPointStalks.linePoint (x : E))).obj ((O.lineTate K h2 n).obj A))).hom
  change z ∈ (LinearMap.charpoly
    ((F.frobenius E).app ((U.pull (RationalPointStalks.linePoint (x : E))).obj ((O.lineTate K h2 n).obj A))).hom).roots at hz
  have hz' : z ∈ (c • f).charpoly.roots := by rw [← hpoly, hi]; exact hz
  have hw := hA E x (z / c) (root_div_of_smul f c hc hz')
  have hq : 0 < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Complex.normSq c = (Fintype.card E : ℝ) ^ ((-2 * n : ℤ) : ℝ) := by
    change Complex.normSq ((Fintype.card E : ℂ)^(-n)) = _
    rw [map_zpow₀, Complex.normSq_natCast, mul_zpow]
    simp only [← Real.rpow_intCast]
    rw [← Real.rpow_add hq]
    congr 1
    push_cast
    ring
  rw [← mul_div_cancel₀ z hc, Complex.normSq_mul, hs, hw, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

/-- Every finite additive-character value is a root of unity, hence weight zero. -/
theorem finite_character_normSq {K : Type} [Field K] [Fintype K]
    (ψ : AddChar K Coefficient) (a : K) : Complex.normSq (complexEquiv (ψ a)) = 1 := by
  have hp : complexEquiv (ψ a) ^ Fintype.card K = 1 := by
    rw [← map_pow, ← ψ.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one, map_one]
  rw [Complex.normSq_eq_norm_sq,
    Complex.norm_eq_one_of_pow_eq_one hp Fintype.card_ne_zero, one_pow]

variable (T : PublishedCoefficientFormulas C U F O B)

include T in
/-- ALL nontrivial standard AS objects at EVERY affine-line point, including zero. -/
theorem artinSchreier_point_weight (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (x : E)
    {z : ℂ} (hz : z ∈ complexRoots C F E ((U.pull (RationalPointStalks.linePoint (K := K) x)).obj
      (O.artinSchreier K h2 ψ))) : Complex.normSq z = 1 := by
  let A := (U.pull (RationalPointStalks.linePoint (K := K) x)).obj (O.artinSchreier K h2 ψ)
  let := B.finite E A
  have hp := congrArg LinearMap.charpoly (T.asFrobenius K h2 ψ hψ E x)
  have hi := ((T.asBasis K h2 ψ hψ E x).toLinearEquiv).charpoly_conj
    ((B.frobenius E).app A).hom
  rw [complex_roots C F B E] at hz
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hz
  have he : a = extension ψ E x := by
    change a ∈ (LinearMap.charpoly ((B.frobenius E).app A).hom).roots at ha
    rw [← hi, hp] at ha
    have hr := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots ha)
    obtain ⟨v, hv⟩ := hr.exists_hasEigenvector
    have h := hv.apply_eq_smul
    change extension ψ E x * v = a * v at h
    exact (mul_right_cancel₀ hv.2 h).symm
  rw [he, finite_character_normSq]

include T in
/-- AS weight zero restricts to the exact unit-point normalization. -/
theorem artinSchreier_pure (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) :
    pureOnUnits C U F K (O.artinSchreier K h2 ψ) 0 := by
  intro E _ _ _ x z hz
  simpa only [Real.rpow_zero] using
    artinSchreier_point_weight C U F O B T K h2 ψ hψ E (x : E) hz

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

include zeroRestriction rawKloostermanWeight pointTateFrobenius in
/-- The exact original normalized Kl3 purity, on the common guarded branch. -/
theorem primitive_kl_pure (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1) :
    LinePurityFromStalks.pureOnUnits (pointStalks C U F p)
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
        ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) 0 := by
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial C O p h2 ψ hψ]
  have h := tate_pure C U F O pointTateIso pointTateFrobenius (ZMod p) h2
    (rawKloosterman3 C O (ZMod p) h2 ψ hψ) 2 1
    (raw_kloosterman_pure C U F O B zeroRestriction rawKloostermanWeight (ZMod p) h2 ψ hψ 3 (by decide))
  change pureOnUnits C U F (ZMod p) _ 0
  simpa only [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_twistOne,
    Int.cast_one, mul_one, sub_self] using h

include T in
/-- The exact original standard AS purity on SAME original point-stalks. -/
theorem primitive_as_pure (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1) :
    LinePurityFromStalks.pureOnUnits (pointStalks C U F p)
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) 0 :=
  artinSchreier_pure C U F O B T (ZMod p) h2 ψ hψ

omit [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include T in
/-- ALL standard AS finite point fibers have rank one, by the actual basis. -/
theorem artinSchreier_point_rank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (z : E) :
    Module.finrank ℂ ((F.fiber E).obj ((U.pull (RationalPointStalks.linePoint (K := K) z)).obj
      (O.artinSchreier K h2 ψ))) = 1 := by
  rw [complex_finrank C F B E]
  exact ((T.asBasis K h2 ψ hψ E z).toLinearEquiv.finrank_eq).trans (Module.finrank_self _)

section Rank
variable (G : NativePointFiberFromUniversalGeometricFibers.GeometricFibers C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  [∀ X, (L X).IsClosedUnderIsomorphisms]
local instance allLocalizations : ∀ X : Scheme, HasDerivedCategory.{mu} (C X) :=
  fun _ => HasDerivedCategory.standard _

variable
  (lineRank : ∀ (K : Type) [Field K], C (StartingSourceMaps.affineLine K) → ℕ)
  (lineRankInterpretation : ∀ (K : Type) [Field K] [Fintype K] (_h2 : (2 : K) ≠ 0)
    (A : C (StartingSourceMaps.affineLine K)),
    SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A →
      lineRank K A = Module.finrank ℂ ((rawGenericFiber K C U G).obj
        ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj
          ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A))))
  (ordinaryKatzRank : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj
        (O.katz K h2 { a with tateTwist := 0 }))) = a.rank)
  (ordinaryTateRank : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (n : ℤ) (A : C (ArithmeticSourceMaps.fiberScheme K)),
    Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj ((O.tate K h2 n).obj A))) =
    Module.finrank ℂ ((rawGenericFiber K C U G).obj
      ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj A)))
  (unequalKatzLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (a : KatzIndex K), a.upper.length ≠ a.lower.length →
      L (ArithmeticSourceMaps.fiberScheme K) (member C O K h2 a))
  (lisseGenericPointRank : ∀ (K : Type) [Field K] [Fintype K]
    (A : C (ArithmeticSourceMaps.fiberScheme K)), L (ArithmeticSourceMaps.fiberScheme K) A →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra K E] (x : Eˣ),
      Module.finrank ℂ ((rawGenericFiber K C U G).obj
        ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).obj A)) =
      Module.finrank ℂ ((F.fiber E).obj ((U.pull (gmPoint K E x)).obj A)))
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (standardASLisse : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient), ψ ≠ 1 → L (StartingSourceMaps.affineLine K) (O.artinSchreier K h2 ψ))

omit [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include zeroRestriction lineRankInterpretation ordinaryKatzRank ordinaryTateRank unequalKatzLisse in
/-- The exact rank of normalized Kl3, using the ALL-lisse observable dictionary. -/
theorem normalized_kloosterman_rank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) :
    lineRank K ((twistOne C O K h2).obj (rawKloosterman3 C O K h2 ψ hψ)) = 3 := by
  have hl := SourceGlobalLissityFromKatzPullbacks.normalizedKl_restriction_lisse
    K C U L O zeroRestriction unequalKatzLisse h2 ψ hψ
  rw [lineRankInterpretation K h2 _ hl]
  let e := SourceGlobalLissityFromKatzPullbacks.normalizedKlRestrictionIso
    K C U O zeroRestriction h2 ψ hψ
  have hi := ((rawGenericFiber K C U G).mapIso
    ((QSTCompactBridgeFromCompactifiedDerivedPushforward.boundedDegreeZero C _).mapIso e)).toLinearEquiv.finrank_eq
  have hr := member_genericRank C U G O ordinaryKatzRank ordinaryTateRank K h2
    (kloostermanIndex ψ hψ 3 (by decide) 1)
  rw [genericFiber_finrank, kloostermanIndex_rank] at hr
  exact hi.trans hr

omit [∀ X, (L X).IsClosedUnderIsomorphisms] [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include T lineRankInterpretation lisseGenericPointRank lissePull standardASLisse in
/-- The SAME arithmetic and geometric fibers determine ALL standard AS ranks. -/
theorem artinSchreier_rank (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) : lineRank K (O.artinSchreier K h2 ψ) = 1 := by
  have hl := lissePull (ArithmeticSourceMaps.localInputMorphism K K) _ (standardASLisse K h2 ψ hψ)
  rw [lineRankInterpretation K h2 _ hl, lisseGenericPointRank K _ hl K 1]
  let e := (U.composition (gmPoint K K 1) (ArithmeticSourceMaps.localInputMorphism K K)).app
    (O.artinSchreier K h2 ψ)
  have hi := ((F.fiber K).mapIso e).toLinearEquiv.finrank_eq
  rw [gmPoint_comp] at hi
  exact hi.trans (artinSchreier_point_rank C U F O B T K h2 ψ hψ K 1)

omit [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include zeroRestriction lineRankInterpretation ordinaryKatzRank ordinaryTateRank unequalKatzLisse in
/-- Exact original primitive operator rank, preserving the nontrivial branch. -/
theorem primitive_kl_rank (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1) :
    lineRank (ZMod p)
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).twistOne
        ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).kloosterman3 ψ)) = 3 := by
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial C O p h2 ψ hψ]
  exact normalized_kloosterman_rank C U O zeroRestriction G L lineRank lineRankInterpretation
    ordinaryKatzRank ordinaryTateRank unequalKatzLisse (ZMod p) h2 ψ hψ

omit [∀ X, (L X).IsClosedUnderIsomorphisms] [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal] in
include T lineRankInterpretation lisseGenericPointRank lissePull standardASLisse in
/-- Exact original standard AS rank, with no selected rank premise. -/
theorem primitive_as_rank (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1) :
    lineRank (ZMod p)
      ((ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2).artinSchreier ψ) = 1 :=
  artinSchreier_rank C U F O B T G L lineRank lineRankInterpretation lisseGenericPointRank
    lissePull standardASLisse (ZMod p) h2 ψ hψ
end Rank

end PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.arithmeticFinite
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.coefficientFinite
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.extendedCoefficientFinite
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.extendedCoefficientFiniteDirect
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.coefficientRoots
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.complexRoots
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.complex_charpoly
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.complex_roots
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.complex_finrank
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.complex_roots_iso
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.pureOnUnits
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.raw_kloosterman_pure
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.tate_pure
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.finite_character_normSq
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.artinSchreier_point_weight
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.artinSchreier_pure
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.primitive_kl_pure
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.primitive_as_pure
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.artinSchreier_point_rank
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.normalized_kloosterman_rank
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.artinSchreier_rank
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.primitive_kl_rank
#print axioms PrimeGap182.TypeIII.PrimitiveRankPurityFromGeneralKatzTheory.primitive_as_rank
