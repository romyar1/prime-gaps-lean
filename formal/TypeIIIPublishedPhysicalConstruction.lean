import TypeIIICoreTraceCoordinates
import TypeIIIPhysicalTorusMorphism
import TypeIIIPublishedCovarianceRules
import TypeIIIPublishedStalkCertificate
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The physical parabolic image from generic cohomological laws

This is a conditional application of published results, not an instance of
the unfinished adic foundations.  The parameter objects form an actual
abelian category, and the core is its literal `Abelian.image` of the given
compact-to-ordinary degree-one comparison.  Neither a core object nor its
lissity, rank, purity or corrected trace is supplied as application data.

The relative curve is the fixed Gm over the parameter torus.  The input
data name its three original factors: the two normalized rank-three
Kloosterman pullbacks, the second dualized, and the linear Artin--Schreier
factor.  Their rank, weight and ramification properties are the Katz and
Artin--Schreier inputs (Katz, GKM, Theorems 4.1.1 and 7.4.3).
Generic tensor and dual laws imply rank nine,
tameness at zero, and all slopes one at infinity, including lambda=1.

The conductor-to-lissity rule is Laumon, *Semi-continuite du conducteur de
Swan*, Theorem 2.1.1(ii), Corollary 2.1.2 and Remark 2.1.3, pp.185--187.
Its intended adic use includes the stable-lattice and finite-coefficient
passage described in `relative_core_lissity.md`; it is not a theorem for
arbitrary discrete complex sheaves.  Relative duality supplies ordinary
degree-one lissity.  Deligne, Weil II, Corollary 3.3.6 supplies purity of
the image, with compact and ordinary base change as specified below.

The finite-field part uses actual stalk functors, Frobenius natural maps,
boundary maps and categorical image factorizations.  The generic GOS and
trace-formula rules concern the original curve input.  Identifying the
arithmetic boundary with the Jordan centralizer is a separately visible
rank-three local-model input.  All claims are consequences of explicit
ordinary parameters; no new global axiom or final Fourier bound is added.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Classical

namespace PrimeGap182.TypeIII.PublishedPhysicalConstruction

universe u v w z

/-- Observables and operations for the original relative-curve inputs.
`Point` indexes all geometric points of the parameter base.  The tame and
break predicates assert the indicated property at every such fiber. -/
structure CurveData (Input : Type u) (Point : Type v) where
  tensor : Input → Input → Input
  dual : Input → Input
  Lisse : Input → Prop
  Pure : Input → ℝ → Prop
  rank : Input → ℕ
  TameZero : Input → Prop
  BreaksLE : Input → ℚ → Prop
  Isoclinic : Input → ℚ → Prop
  swanZero : Input → Point → ℕ
  swanInfinity : Input → Point → ℕ

/-- The usual tensor/dual and break-decomposition rules, applied to
arbitrary relative inputs, not to a preselected correlation core. -/
structure CurveRules {Input : Type u} {Point : Type v}
    (D : CurveData Input Point) : Prop where
  tensor_lisse : ∀ A B, D.Lisse A → D.Lisse B → D.Lisse (D.tensor A B)
  tensor_rank : ∀ A B, D.Lisse A → D.Lisse B →
    D.rank (D.tensor A B) = D.rank A * D.rank B
  tensor_pure : ∀ A B a b, D.Pure A a → D.Pure B b →
    D.Pure (D.tensor A B) (a + b)
  dual_lisse : ∀ A, D.Lisse A → D.Lisse (D.dual A)
  dual_rank : ∀ A, D.Lisse A → D.rank (D.dual A) = D.rank A
  dual_pure : ∀ A a, D.Lisse A → D.Pure A a → D.Pure (D.dual A) (-a)
  tensor_tame : ∀ A B, D.TameZero A → D.TameZero B → D.TameZero (D.tensor A B)
  dual_tame : ∀ A, D.TameZero A → D.TameZero (D.dual A)
  tensor_breaks : ∀ A B r, D.BreaksLE A r → D.BreaksLE B r →
    D.BreaksLE (D.tensor A B) r
  dual_breaks : ∀ A r, D.BreaksLE A r → D.BreaksLE (D.dual A) r
  tensor_unequal_breaks : ∀ A B r s, r < s → D.BreaksLE A r →
    D.Isoclinic B s → D.Isoclinic (D.tensor A B) s
  dual_isoclinic : ∀ A r, D.Isoclinic A r → D.Isoclinic (D.dual A) r
  tame_swan : ∀ A, D.TameZero A → ∀ t, D.swanZero A t = 0
  slope_one_swan : ∀ A, D.Isoclinic A 1 → ∀ t, D.swanInfinity A t = D.rank A

/-- The three original factors on Gm times the parameter torus.  The
second Kloosterman factor is supplied before taking its actual dual.
All local assertions include every unit lambda and xi, not only generic
lambda.  In particular no six-wild-phase assertion is a field. -/
structure KloostermanInputData {Input : Type u} {Point : Type v}
    (D : CurveData Input Point) where
  first : Input
  second : Input
  additive : Input
  first_lisse : D.Lisse first
  second_lisse : D.Lisse second
  additive_lisse : D.Lisse additive
  first_rank : D.rank first = 3
  second_rank : D.rank second = 3
  additive_rank : D.rank additive = 1
  first_pure : D.Pure first 0
  second_pure : D.Pure second 0
  additive_pure : D.Pure additive 0
  first_tame : D.TameZero first
  second_tame : D.TameZero second
  additive_tame : D.TameZero additive
  first_breaks : D.BreaksLE first (1 / 3)
  second_breaks : D.BreaksLE second (1 / 3)
  additive_slope : D.Isoclinic additive 1

namespace KloostermanInputData

variable {Input : Type u} {Point : Type v} {D : CurveData Input Point}
  (K : KloostermanInputData D) (R : CurveRules D)

/-- The same K(x) tensor K(lambda*x)^dual tensor AS(xi*x) input. -/
def input : Input := D.tensor (D.tensor K.first (D.dual K.second)) K.additive

include R

theorem input_lisse : D.Lisse K.input :=
  R.tensor_lisse _ _ (R.tensor_lisse _ _ K.first_lisse
    (R.dual_lisse _ K.second_lisse)) K.additive_lisse

theorem input_rank : D.rank K.input = 9 := by
  rw [input, R.tensor_rank _ _ (R.tensor_lisse _ _ K.first_lisse
    (R.dual_lisse _ K.second_lisse)) K.additive_lisse,
    R.tensor_rank _ _ K.first_lisse (R.dual_lisse _ K.second_lisse),
    R.dual_rank _ K.second_lisse, K.first_rank, K.second_rank, K.additive_rank]

theorem input_pure : D.Pure K.input 0 := by
  have hd : D.Pure (D.dual K.second) 0 := by
    simpa only [neg_zero] using R.dual_pure _ 0 K.second_lisse K.second_pure
  simpa only [input, add_zero] using R.tensor_pure _ _ (0 + 0) 0
    (R.tensor_pure _ _ 0 0 K.first_pure hd) K.additive_pure

theorem input_tame : D.TameZero K.input :=
  R.tensor_tame _ _ (R.tensor_tame _ _ K.first_tame
    (R.dual_tame _ K.second_tame)) K.additive_tame

/-- Unequal slopes make all nine slopes one even when lambda=1. -/
theorem input_slope_one : D.Isoclinic K.input 1 :=
  R.tensor_unequal_breaks _ _ (1 / 3) 1 (by norm_num)
    (R.tensor_breaks _ _ _ K.first_breaks (R.dual_breaks _ _ K.second_breaks))
    K.additive_slope

theorem input_swan (t : Point) :
    D.swanZero K.input t = 0 ∧ D.swanInfinity K.input t = 9 := by
  exact ⟨R.tame_swan _ (K.input_tame R) t,
    (R.slope_one_swan _ (K.input_slope_one R) t).trans (K.input_rank R)⟩

theorem dual_input_swan (t : Point) :
    D.swanZero (D.dual K.input) t = 0 ∧ D.swanInfinity (D.dual K.input) t = 9 := by
  refine ⟨R.tame_swan _ (R.dual_tame _ (K.input_tame R)) t, ?_⟩
  rw [R.slope_one_swan _ (R.dual_isoclinic _ _ (K.input_slope_one R)) t,
    R.dual_rank _ (K.input_lisse R), K.input_rank R]

theorem input_conductor (t : Point) :
    (D.rank K.input + D.swanZero K.input t) +
      (D.rank K.input + D.swanInfinity K.input t) = 27 := by
  rw [K.input_rank R, (K.input_swan R t).1, (K.input_swan R t).2]

theorem dual_input_conductor (t : Point) :
    (D.rank (D.dual K.input) + D.swanZero (D.dual K.input) t) +
      (D.rank (D.dual K.input) + D.swanInfinity (D.dual K.input) t) = 27 := by
  rw [R.dual_rank _ (K.input_lisse R), K.input_rank R,
    (K.dual_input_swan R t).1, (K.dual_input_swan R t).2]

end KloostermanInputData

/-- The original degree-one cohomology operations and their natural
comparison for the fixed relative curve.  In the intended realization
these are R¹f! and R¹f*, not freely chosen final core objects. -/
structure CohomologyData (Input : Type u) (C : Type w) [Category.{z} C] where
  compact : Input → C
  ordinary : Input → C
  comparison : ∀ A, compact A ⟶ ordinary A

/-- Observables and the actual dual(-1) operation on parameter sheaves.
The signed operation is tensor with the constant Weil sheaf whose
degree-one geometric Frobenius is -1. -/
structure ParameterData (C : Type w) where
  Lisse : C → Prop
  Pure : C → ℝ → Prop
  dualTateMinusOne : C → C
  signed : C → C

/-- The literal categorical image of the original comparison. -/
def parabolicCore {Input : Type u} {C : Type w} [Category.{z} C] [Abelian C]
    (H : CohomologyData Input C) (A : Input) : C :=
  Abelian.image (H.comparison A)

/-- Generic lisse-image, duality, conductor and pure-image laws.

The `image_pure` rule is the standard deduction from compact/ordinary
base change and Weil II 3.3.6.  The positive-slope hypotheses exclude
Hc⁰ and Hc² for the input and its dual.  When both degree-one compact
families are lisse, relative duality therefore gives base change for the
ordinary family, and exact stalk pullback identifies the original image
with im(Hc¹→H¹).  This is a rule for every such lisse pure curve input; no particular rank,
Kloosterman function or corrected trace occurs in it.
-/
structure CohomologyRules {Input : Type u} {Point : Type v}
    {C : Type w} [Category.{z} C] [Abelian C]
    (D : CurveData Input Point) (H : CohomologyData Input C)
    (P : ParameterData C) : Prop where
  compact_lisse : ∀ A, D.Lisse A →
    (∃ N : ℕ, ∀ t, (D.rank A + D.swanZero A t) +
      (D.rank A + D.swanInfinity A t) = N) → P.Lisse (H.compact A)
  ordinary_duality : ∀ A, D.Lisse A → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact (D.dual A)) →
    Nonempty (H.ordinary A ≅ P.dualTateMinusOne (H.compact (D.dual A)))
  dualTate_lisse : ∀ A, P.Lisse A → P.Lisse (P.dualTateMinusOne A)
  lisse_of_iso : ∀ A B, Nonempty (A ≅ B) → P.Lisse B → P.Lisse A
  image_lisse : ∀ A B (f : A ⟶ B), P.Lisse A → P.Lisse B →
    P.Lisse (Abelian.image f)
  image_pure : ∀ A a, D.Lisse A → D.Pure A a →
    D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact A) → P.Lisse (H.compact (D.dual A)) →
      P.Pure (parabolicCore H A) (a + 1)
  signed_lisse : ∀ A, P.Lisse A → P.Lisse (P.signed A)
  signed_pure : ∀ A a, P.Pure A a → P.Pure (P.signed A) a
  dualTate_pure : ∀ A a, P.Lisse A → P.Pure A a →
    P.Pure (P.dualTateMinusOne A) (2 - a)

section CoreGeometry

variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  (K : KloostermanInputData D) (R : CurveRules D) (G : CohomologyRules D H P)

include R G

theorem compact_lisse : P.Lisse (H.compact K.input) :=
  G.compact_lisse _ (K.input_lisse R) ⟨27, K.input_conductor R⟩

theorem compact_dual_lisse : P.Lisse (H.compact (D.dual K.input)) :=
  G.compact_lisse _ (R.dual_lisse _ (K.input_lisse R)) ⟨27, K.dual_input_conductor R⟩

theorem ordinary_lisse : P.Lisse (H.ordinary K.input) :=
  G.lisse_of_iso _ _ (G.ordinary_duality _ (K.input_lisse R)
    (R.dual_isoclinic _ _ (K.input_slope_one R)) (compact_dual_lisse K R G))
    (G.dualTate_lisse _ (compact_dual_lisse K R G))

/-- The actual image is lisse on the whole parameter torus. -/
theorem core_lisse : P.Lisse (parabolicCore H K.input) :=
  G.image_lisse _ _ _ (compact_lisse K R G) (ordinary_lisse K R G)

/-- Weight one is obtained from the generic pure-image theorem. -/
theorem core_pure : P.Pure (parabolicCore H K.input) 1 := by
  simpa only [zero_add] using G.image_pure _ 0 (K.input_lisse R) (K.input_pure R)
    (K.input_slope_one R) (R.dual_isoclinic _ _ (K.input_slope_one R))
    (compact_lisse K R G) (compact_dual_lisse K R G)

theorem signed_core_lisse : P.Lisse (P.signed (parabolicCore H K.input)) :=
  G.signed_lisse _ (core_lisse K R G)

theorem signed_core_pure : P.Pure (P.signed (parabolicCore H K.input)) 1 :=
  G.signed_pure _ _ (core_pure K R G)

/-- A conjugated factor is the dual twisted by -1; its weight is still
one.  The ordinary dual alone would have weight -1. -/
theorem conjugate_signed_core_pure :
    P.Pure (P.dualTateMinusOne (P.signed (parabolicCore H K.input))) 1 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
    G.dualTate_pure _ 1 (signed_core_lisse K R G) (signed_core_pure K R G)

end CoreGeometry

section ActualStalkImage

variable {Input : Type u} {C : Type w} [Category.{z} C] [Abelian C]
  (H : CohomologyData Input C) (F : C ⥤ ModuleCat.{w} ℂ)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exact stalk pullback identifies the same categorical image with
the image of the original stalk comparison.  This is proved from
Mathlib's kernel/cokernel preservation, not an added comparison premise. -/
def coreStalkImageIso (A : Input) :
    F.obj (parabolicCore H A) ≅ Abelian.image (F.map (H.comparison A)) :=
  Abelian.PreservesImage.iso F (H.comparison A)

/-- The original image quotient on the actual stalk. -/
def coreStalkQuotient (A : Input) :
    F.obj (H.compact A) →ₗ[ℂ] F.obj (parabolicCore H A) :=
  (F.map (Abelian.factorThruImage (H.comparison A))).hom

/-- The original image inclusion on the actual stalk. -/
def coreStalkInclusion (A : Input) :
    F.obj (parabolicCore H A) →ₗ[ℂ] F.obj (H.ordinary A) :=
  (F.map (Abelian.image.ι (H.comparison A))).hom

theorem coreStalkQuotient_surjective (A : Input) :
    Function.Surjective (coreStalkQuotient H F A) :=
  (ModuleCat.epi_iff_surjective (F.map (Abelian.factorThruImage (H.comparison A)))).mp
    inferInstance

theorem coreStalkInclusion_injective (A : Input) :
    Function.Injective (coreStalkInclusion H F A) :=
  (ModuleCat.mono_iff_injective (F.map (Abelian.image.ι (H.comparison A)))).mp
    inferInstance

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem coreStalk_factorization (A : Input) :
    (coreStalkInclusion H F A).comp (coreStalkQuotient H F A) =
      (F.map (H.comparison A)).hom := by
  change (F.map (Abelian.factorThruImage (H.comparison A)) ≫
    F.map (Abelian.image.ι (H.comparison A))).hom = _
  rw [← F.map_comp, Abelian.image.fac]

theorem coreStalkQuotient_ker (A : Input) :
    LinearMap.ker (coreStalkQuotient H F A) =
      LinearMap.ker (F.map (H.comparison A)).hom := by
  ext x
  change coreStalkQuotient H F A x = 0 ↔ (F.map (H.comparison A)).hom x = 0
  rw [← coreStalk_factorization H F A]
  change _ ↔ coreStalkInclusion H F A (coreStalkQuotient H F A x) = 0
  rw [← map_zero (coreStalkInclusion H F A)]
  exact (coreStalkInclusion_injective H F A).eq_iff.symm

/-- A literal arithmetic identification of the boundary injection with
the Jordan centralizer.  The exactness field is for Hc¹→H¹, not for a
supplied rank-six space; the latter is the categorical image above.
Its geometric proof uses the boundary exact sequence and the rank-three
Katz local model.  The fields do not assert a core rank or trace. -/
structure OriginBoundaryModel (A : Input) (Fr : F ⟶ F) (q : ℂ) (hq : q ≠ 0) where
  boundary : jordanThreeCentralizer ℂ →ₗ[ℂ] F.obj (H.compact A)
  injective : Function.Injective boundary
  exact : LinearMap.range boundary = LinearMap.ker (F.map (H.comparison A)).hom
  frobenius : (Fr.app (H.compact A)).hom.comp boundary =
    boundary.comp (jordanThreeCentralizerConjugation q hq)

/-- The original boundary injection and original image quotient form
the existing exact-sequence input.  The image Frobenius is the actual
natural stalk Frobenius, and its commuting square is naturality. -/
def OriginBoundaryModel.jordanData (A : Input) (Fr : F ⟶ F) (q : ℂ) (hq : q ≠ 0)
    (B : OriginBoundaryModel H F A Fr q hq) :
    PublishedParabolicTrace.JordanBoundaryData q hq
      (F.obj (H.compact A)) (F.obj (parabolicCore H A)) where
  boundary := B.boundary
  quotient := coreStalkQuotient H F A
  boundary_injective := B.injective
  quotient_surjective := coreStalkQuotient_surjective H F A
  exact := B.exact.trans (coreStalkQuotient_ker H F A).symm
  compactFrobenius := (Fr.app (H.compact A)).hom
  parabolicFrobenius := (Fr.app (parabolicCore H A)).hom
  boundary_frobenius := B.frobenius
  quotient_frobenius := by
    exact congrArg ModuleCat.Hom.hom
      (Fr.naturality (Abelian.factorThruImage (H.comparison A))).symm

end ActualStalkImage

section ArithmeticFiber

variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat.{w} ℂ) (Fr : F ⟶ F)
  (L : Type) [Field L] [Fintype L]

/-- The input trace at the chosen finite-field fiber.  It is a trace of
the original curve sheaf, before any compact cohomology is taken. -/
structure CurveTraceData (D : CurveData Input Point) (L : Type) [Field L] where
  point : Point
  trace : Input → Lˣ → ℂ

/-- The generic fiber rules are the trace formula and GOS on Gm, with
Hc⁰=Hc²=0 from positive slopes at infinity in the input and its dual.
The displayed rank is derived from Swan conductors; no rank-nine or
rank-six assertion is a field.  The trace is the original point sum.
Finite dimensionality is explicit, preventing a vacuous infinite-space
interpretation of `finrank` or `LinearMap.trace`. -/
structure CurveFiberRules (T : CurveTraceData D L) : Prop where
  compact_finite : ∀ A, D.Lisse A → FiniteDimensional ℂ (F.obj (H.compact A))
  compact_rank : ∀ A, D.Lisse A → D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    Module.finrank ℂ (F.obj (H.compact A)) =
      D.swanZero A T.point + D.swanInfinity A T.point
  compact_trace : ∀ A, D.Lisse A → D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    LinearMap.trace ℂ (F.obj (H.compact A)) (Fr.app (H.compact A)).hom =
      -∑ x : Lˣ, T.trace A x
  tensor_trace : ∀ A B x, T.trace (D.tensor A B) x = T.trace A x * T.trace B x
  dual_weight_zero_trace : ∀ A, D.Lisse A → D.Pure A 0 → ∀ x,
    T.trace (D.dual A) x = star (T.trace A x)

/-- Arithmetic trace of the original three factors.  The data assert
the normalized rank-three Kloosterman and Artin--Schreier trace formulas,
not the trace of their cohomology or of an already corrected kernel. -/
structure KloostermanTraceData (K : KloostermanInputData D)
    (T : CurveTraceData D L) (ψ : AddChar L ℂ) (lambda xi : Lˣ) : Prop where
  first_trace : ∀ x, T.trace K.first x = FiniteFieldSums.kl3 ψ (x : L)
  second_trace : ∀ x, T.trace K.second x = FiniteFieldSums.kl3 ψ (lambda * (x : L))
  additive_trace : ∀ x, T.trace K.additive x = ψ (xi * (x : L))

variable {D H F Fr L}
  (K : KloostermanInputData D) (R : CurveRules D)
  (T : CurveTraceData D L) (V : CurveFiberRules D H F Fr L T)

include R V

omit [Abelian C] in
/-- GOS gives the compact rank nine from the proved local conductors. -/
theorem compact_rank_nine : Module.finrank ℂ (F.obj (H.compact K.input)) = 9 := by
  rw [V.compact_rank _ (K.input_lisse R) (K.input_slope_one R)
    (R.dual_isoclinic _ _ (K.input_slope_one R)),
    (K.input_swan R T.point).1, (K.input_swan R T.point).2]

omit R [Abelian C] in
/-- Trace multiplication and the weight-zero dual rule recover the
literal Kloosterman-tensor point sum. -/
theorem input_point_sum (ψ : AddChar L ℂ) (lambda xi : Lˣ)
    (A : KloostermanTraceData D L K T ψ lambda xi) :
    (∑ x : Lˣ, T.trace K.input x) =
      FiniteFieldSums.parabolicInputSum ψ lambda xi := by
  unfold KloostermanInputData.input FiniteFieldSums.parabolicInputSum
  apply Finset.sum_congr rfl
  intro x _
  rw [V.tensor_trace, V.tensor_trace,
    V.dual_weight_zero_trace _ K.second_lisse K.second_pure,
    A.first_trace, A.second_trace, A.additive_trace]

omit [Abelian C] in
theorem compact_trace_input_sum (ψ : AddChar L ℂ) (lambda xi : Lˣ)
    (A : KloostermanTraceData D L K T ψ lambda xi) :
    LinearMap.trace ℂ (F.obj (H.compact K.input))
        (Fr.app (H.compact K.input)).hom =
      -FiniteFieldSums.parabolicInputSum ψ lambda xi := by
  rw [V.compact_trace _ (K.input_lisse R) (K.input_slope_one R)
    (R.dual_isoclinic _ _ (K.input_slope_one R)),
    input_point_sum K T V ψ lambda xi A]

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (B : OriginBoundaryModel H F K.input Fr (Fintype.card L : ℂ)
    (PublishedParabolicTrace.complexCard_ne_zero L))

include B

/-- The actual stalk of the original image has rank six, by GOS, the
boundary sequence and the already checked Jordan-centralizer dimension. -/
theorem core_stalk_rank_six :
    Module.finrank ℂ (F.obj (parabolicCore H K.input)) = 6 := by
  let := V.compact_finite _ (K.input_lisse R)
  exact (B.jordanData H F K.input Fr _ _).finrank_eq_six (compact_rank_nine K R T V)

/-- The actual natural Frobenius on the same image stalk has the
negative corrected trace.  No sign twist has yet been applied. -/
theorem core_stalk_trace (ψ : AddChar L ℂ) (lambda xi : Lˣ)
    (A : KloostermanTraceData D L K T ψ lambda xi) :
    LinearMap.trace ℂ (F.obj (parabolicCore H K.input))
        (Fr.app (parabolicCore H K.input)).hom =
      -(FiniteFieldSums.parabolicInputSum ψ lambda xi +
        FiniteFieldSums.coreCorrection L) := by
  let := V.compact_finite _ (K.input_lisse R)
  exact (B.jordanData H F K.input Fr _ _).trace_eq _
    (compact_trace_input_sum K R T V ψ lambda xi A)

/-- The degree-d constant sign twist acts on the actual image
endomorphism.  The resulting exponent is d+1 over every finite extension. -/
theorem signed_core_stalk_trace (ψ : AddChar L ℂ) (lambda xi : Lˣ)
    (A : KloostermanTraceData D L K T ψ lambda xi) (d : ℕ) :
    LinearMap.trace ℂ (F.obj (parabolicCore H K.input))
        (((-1 : ℂ) ^ d) • (Fr.app (parabolicCore H K.input)).hom) =
      (-1 : ℂ) ^ (d + 1) * (FiniteFieldSums.parabolicInputSum ψ lambda xi +
        FiniteFieldSums.coreCorrection L) := by
  let := V.compact_finite _ (K.input_lisse R)
  exact (B.jordanData H F K.input Fr _ _).signed_trace_eq d _
    (compact_trace_input_sum K R T V ψ lambda xi A)

end ArithmeticFiber

section BoundaryConstruction

variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  (D : CurveData Input Point) (H : CohomologyData Input C)
  (F : C ⥤ ModuleCat.{w} ℂ) (Fr : F ⟶ F)

/-- The original sum of inertia-invariant boundary spaces and its map
to compact cohomology.  No exactness or specific local-model assertion
is part of these operations. -/
structure BoundaryCohomologyData where
  space : Input → ModuleCat.{w} ℂ
  toCompact : ∀ A, space A →ₗ[ℂ] F.obj (H.compact A)
  frobenius : ∀ A, space A →ₗ[ℂ] space A

/-- Positive slope at infinity kills global invariants and gives the
boundary injection. Exactness in the stalk of the relative ordinary
cohomology additionally uses tame ramification at zero: together with
slope one and constant rank, this is the constant-conductor class for
whole-base ordinary base change. Naturality gives the Frobenius square. -/
structure BoundaryCohomologyRules (B : BoundaryCohomologyData H F) : Prop where
  injective : ∀ A, D.Lisse A → D.Isoclinic A 1 →
    Function.Injective (B.toCompact A)
  exact : ∀ A, D.Lisse A → D.TameZero A → D.Isoclinic A 1 →
    LinearMap.range (B.toCompact A) = LinearMap.ker (F.map (H.comparison A)).hom
  frobenius : ∀ A, (Fr.app (H.compact A)).hom.comp (B.toCompact A) =
    (B.toCompact A).comp (B.frobenius A)

/-- The arithmetic local Kloosterman model identifies the full boundary
space with the actual Jordan centralizer, including its Frobenius.
This is the remaining local-model identification, not a rank-six,
corrected-trace, cohomological exactness or lissity hypothesis.
The invariant space at infinity is zero by the already proved slope
one statement.  At zero the normalized regular-unipotent rank-three
model, including the scalar-lambda pullback, gives this equivalence. -/
structure KloostermanBoundaryData (K : KloostermanInputData D)
    (B : BoundaryCohomologyData H F) (q : ℂ) (hq : q ≠ 0) where
  identification : jordanThreeCentralizer ℂ ≃ₗ[ℂ] B.space K.input
  frobenius : (B.frobenius K.input).comp identification.toLinearMap =
    identification.toLinearMap.comp (jordanThreeCentralizerConjugation q hq)

variable {D H F Fr}
  (K : KloostermanInputData D) (R : CurveRules D)
  (B : BoundaryCohomologyData H F) (BR : BoundaryCohomologyRules D H F Fr B)
  (q : ℂ) (hq : q ≠ 0) (J : KloostermanBoundaryData D H F K B q hq)

/-- The former direct boundary-model premise is constructed from the
generic boundary sequence and the lower-level arithmetic local model. -/
def originBoundaryModel : OriginBoundaryModel H F K.input Fr q hq where
  boundary := (B.toCompact K.input).comp J.identification.toLinearMap
  injective := (BR.injective _ (K.input_lisse R) (K.input_slope_one R)).comp
    J.identification.injective
  exact := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact BR.exact _ (K.input_lisse R) (K.input_tame R) (K.input_slope_one R)
  frobenius := by
    rw [← LinearMap.comp_assoc, BR.frobenius, LinearMap.comp_assoc,
      J.frobenius, ← LinearMap.comp_assoc]

end BoundaryConstruction

section ConstantSign

variable {C : Type w} [Category.{z} C] (P : ParameterData C)
  (F : C ⥤ ModuleCat.{w} ℂ) (Fr : F ⟶ F) (d : ℕ)

/-- Tensoring with the constant sign Weil sheaf has this generic
stalk comparison.  The Frobenius on the signed object is already the
natural action; it is not defined by a final scalar eigenvalue. -/
structure SignStalkComparison where
  comparison : ∀ A, F.obj (P.signed A) ≃ₗ[ℂ] F.obj A
  frobenius : ∀ A, (comparison A).conj (Fr.app (P.signed A)).hom =
    ((-1 : ℂ) ^ d) • (Fr.app A).hom

/-- The generic sign comparison transports the trace of the actual
signed sheaf, with the extension degree retained. -/
theorem SignStalkComparison.trace (S : SignStalkComparison P F Fr d) (A : C) :
    LinearMap.trace ℂ (F.obj (P.signed A)) (Fr.app (P.signed A)).hom =
      LinearMap.trace ℂ (F.obj A) (((-1 : ℂ) ^ d) • (Fr.app A).hom) := by
  rw [← S.frobenius A, LinearMap.trace_conj']

end ConstantSign

section SignedSheafTrace

variable {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  (P : ParameterData C) (F : C ⥤ ModuleCat.{w} ℂ) (Fr : F ⟶ F)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (L : Type) [Field L] [Fintype L]
  (K : KloostermanInputData D) (R : CurveRules D)
  (T : CurveTraceData D L) (V : CurveFiberRules D H F Fr L T)
  (B : OriginBoundaryModel H F K.input Fr (Fintype.card L : ℂ)
    (PublishedParabolicTrace.complexCard_ne_zero L))

include R V B

/-- The trace formula now concerns the actual signed parameter object,
rather than only a sign-scaled endomorphism of an unnamed core space. -/
theorem signed_sheaf_trace (ψ : AddChar L ℂ) (lambda xi : Lˣ)
    (A : KloostermanTraceData D L K T ψ lambda xi) (d : ℕ)
    (S : SignStalkComparison P F Fr d) :
    LinearMap.trace ℂ (F.obj (P.signed (parabolicCore H K.input)))
        (Fr.app (P.signed (parabolicCore H K.input))).hom =
      (-1 : ℂ) ^ (d + 1) * (FiniteFieldSums.parabolicInputSum ψ lambda xi +
        FiniteFieldSums.coreCorrection L) := by
  rw [S.trace P F Fr d]
  exact signed_core_stalk_trace K R T V B ψ lambda xi A d

/-- Literal physical substitution in the actual signed-sheaf trace,
over every finite extension.  The unit hypotheses guarantee that the
point lies in the whole parameter torus; lambda is permitted to be one. -/
theorem signed_sheaf_kernel_trace (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (α m n x y : L) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (A : KloostermanTraceData D L K T (FiniteFieldSums.traceAddChar p L)
      (Units.mk0 (FiniteFieldSums.coreLambda m n x y)
        (FiniteFieldSums.coreLambda_ne_zero m n x y hm hn hx hy))
      (Units.mk0 (FiniteFieldSums.coreXi α m x y)
        (FiniteFieldSums.coreXi_ne_zero α m x y hα hm hx hy)))
    (S : SignStalkComparison P F Fr (Module.finrank (ZMod p) L)) :
    LinearMap.trace ℂ (F.obj (P.signed (parabolicCore H K.input)))
        (Fr.app (P.signed (parabolicCore H K.input))).hom =
      FiniteFieldSums.extensionSign p L *
        FiniteFieldSums.correctedKernel (FiniteFieldSums.traceAddChar p L) α m n x y := by
  rw [signed_sheaf_trace P F Fr L K R T V B _ _ _ A _ S]
  exact FiniteFieldSums.signed_parabolicInputSum_eq_correctedKernel
    p α m n x y hα hm hn hx hy

end SignedSheafTrace

open AlgebraicGeometry
open scoped MonoidalCategory

/-- Arithmetic fibers of the parameter Weil-sheaf category.  All
operators are actual natural maps on its chosen fiber functors; geometric
objects without a Weil structure are not objects of this category.
Finite dimensionality is the usual constructibility condition. -/
structure TorusArithmeticData (p : ℕ) [Fact p.Prime]
    (C : Type w) [Category.{z} C] where
  fiber : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    Lˣ → Lˣ → C ⥤ ModuleCat.{w} ℂ
  frobenius : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, fiber L x y ⟶ fiber L x y
  finite : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ (x y : Lˣ) (A : C), FiniteDimensional ℂ ((fiber L x y).obj A)

/-- The actual trace of the specified Weil object's arithmetic stalk. -/
def TorusArithmeticData.trace {p : ℕ} [Fact p.Prime] {C : Type w} [Category.{z} C]
    (T : TorusArithmeticData p C) (L : Type) [Field L] [Fintype L]
    [Algebra (ZMod p) L] (A : C) (x y : Lˣ) : ℂ :=
  LinearMap.trace ℂ ((T.fiber L x y).obj A) ((T.frobenius L x y).app A).hom

/-- Inverse image is indexed by genuine scheme morphisms of the actual
quotient torus.  It is not indexed by arbitrary functions on finite points. -/
structure TorusOperationData (p : ℕ) [Fact p.Prime]
    (C : Type w) [Category.{z} C] where
  pullback : (PhysicalTorusMorphism.torusScheme (ZMod p) ⟶
    PhysicalTorusMorphism.torusScheme (ZMod p)) → C ⥤ C

/-- Generic pullback, actual tensor and weight-one dual(-1) laws for
Weil sheaves on the torus.  The pullback trace law requires equality of
the genuine scheme points after the given genuine morphism. -/
structure TorusRules {p : ℕ} [Fact p.Prime] {C : Type w}
    [Category.{z} C] [MonoidalCategory C]
    (P : ParameterData C) (O : TorusOperationData p C) (T : TorusArithmeticData p C) : Prop where
  pullback_lisse : ∀ f A, P.Lisse A → P.Lisse ((O.pullback f).obj A)
  pullback_pure : ∀ f A a, P.Pure A a → P.Pure ((O.pullback f).obj A) a
  unit_lisse : P.Lisse (𝟙_ C)
  unit_pure : P.Pure (𝟙_ C) 0
  tensor_lisse : ∀ A B, P.Lisse A → P.Lisse B → P.Lisse (A ⊗ B)
  tensor_pure : ∀ A B a b, P.Pure A a → P.Pure B b → P.Pure (A ⊗ B) (a + b)
  unit_trace : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, T.trace L (𝟙_ C) x y = 1
  tensor_trace : ∀ A B, P.Lisse A → P.Lisse B →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : Lˣ,
      T.trace L (A ⊗ B) x y = T.trace L A x y * T.trace L B x y
  dualTate_trace : ∀ A, P.Lisse A → P.Pure A 1 →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : Lˣ,
      T.trace L (P.dualTateMinusOne A) x y = star (T.trace L A x y)
  pullback_trace : ∀ f A, P.Lisse A →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y x' y' : Lˣ,
      PhysicalTorusMorphism.schemePoint (K := ZMod p) x y ≫ f =
        PhysicalTorusMorphism.schemePoint (K := ZMod p) x' y' →
      T.trace L ((O.pullback f).obj A) x y = T.trace L A x' y'

/-- The actual relative cohomology and arithmetic local-model
realizations, at every finite extension and every unit parameter pair.
The cohomological rules are generic in the curve input.  The only
Kloosterman-specific arithmetic data are its original three point traces
and the rank-three origin model.  No corrected trace, core rank, core
lissity, Fourier support or norm estimate is assumed.

For complexity applications the three input objects still need their
explicit source-recipe identification as pullbacks of one fixed Kl3 and
AS along x, lambda*x and xi*x.  Rank and fiber Swan data alone do not
bound complexity in the parameter directions.
-/
structure CohomologicalRealization {p : ℕ} [Fact p.Prime]
    {Input : Type u} {Point : Type v} {C : Type w} [Category.{z} C] [Abelian C]
    (D : CurveData Input Point) (H : CohomologyData Input C) (P : ParameterData C)
    (K : KloostermanInputData D) (T : TorusArithmeticData p C) where
  additive : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, (T.fiber L x y).Additive
  finiteLimits : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, PreservesFiniteLimits (T.fiber L x y)
  finiteColimits : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, PreservesFiniteColimits (T.fiber L x y)
  curveTrace : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    Lˣ → Lˣ → CurveTraceData D L
  fiberRules : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, CurveFiberRules D H (T.fiber L x y) (T.frobenius L x y) L (curveTrace L x y)
  originalTraces : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, KloostermanTraceData D L K (curveTrace L x y)
      (FiniteFieldSums.traceAddChar p L) x y
  boundary : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, BoundaryCohomologyData H (T.fiber L x y)
  boundaryRules : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, BoundaryCohomologyRules D H (T.fiber L x y) (T.frobenius L x y)
      (boundary L x y)
  localBoundary : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, KloostermanBoundaryData D H (T.fiber L x y) K (boundary L x y)
      (Fintype.card L : ℂ) (PublishedParabolicTrace.complexCard_ne_zero L)
  sign : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, SignStalkComparison P (T.fiber L x y) (T.frobenius L x y)
      (Module.finrank (ZMod p) L)

section PhysicalEntries

variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  (K : KloostermanInputData D) (R : CurveRules D) (G : CohomologyRules D H P)
  (O : TorusOperationData p C) (T : TorusArithmeticData p C)
  (TR : TorusRules P O T) (M : CohomologicalRealization D H P K T)

include R M in
omit [MonoidalCategory C] in
/-- All-extension corrected trace of the actual signed image, before
any physical pullback.  It is deduced from the preceding cohomology rules. -/
theorem signed_core_parameter_trace (L : Type) [Field L] [Fintype L]
    [Algebra (ZMod p) L] (lambda xi : Lˣ) :
    T.trace L (P.signed (parabolicCore H K.input)) lambda xi =
      FiniteFieldSums.extensionSign p L *
        (FiniteFieldSums.parabolicInputSum (FiniteFieldSums.traceAddChar p L) lambda xi +
          FiniteFieldSums.coreCorrection L) := by
  let := M.additive L lambda xi
  let := M.finiteLimits L lambda xi
  let := M.finiteColimits L lambda xi
  exact signed_sheaf_trace P _ _ L K R _ (M.fiberRules L lambda xi)
    (originBoundaryModel K R (M.boundary L lambda xi) (M.boundaryRules L lambda xi)
      _ _ (M.localBoundary L lambda xi)) _ _ _ (M.originalTraces L lambda xi) _
    (M.sign L lambda xi)

/-- Pullback of the same signed image along the genuine physical map. -/
def pulledEntry (α m n : (ZMod p)ˣ) : C :=
  (O.pullback (PhysicalTorusMorphism.physicalMorphism (ZMod p) α m n)).obj
    (P.signed (parabolicCore H K.input))

include R G TR in
theorem pulledEntry_lisse (α m n : (ZMod p)ˣ) : P.Lisse (pulledEntry (H := H) (P := P) K O α m n) :=
  TR.pullback_lisse _ _ (signed_core_lisse K R G)

include R G TR in
theorem pulledEntry_pure (α m n : (ZMod p)ˣ) : P.Pure (pulledEntry (H := H) (P := P) K O α m n) 1 :=
  TR.pullback_pure _ _ _ (signed_core_pure K R G)

include R G TR M in
/-- The actual scheme-point identity makes the pullback trace the
literal corrected kernel at every extension-field unit pair. -/
theorem pulledEntry_trace (α m n : (ZMod p)ˣ) (L : Type) [Field L] [Fintype L]
    [Algebra (ZMod p) L] (x y : Lˣ) :
    T.trace L (pulledEntry (H := H) (P := P) K O α m n) x y =
      FiniteFieldSums.extensionSign p L * FiniteFieldSums.correctedKernel
        (FiniteFieldSums.traceAddChar p L) (algebraMap (ZMod p) L (α : ZMod p))
        (algebraMap (ZMod p) L (m : ZMod p)) (algebraMap (ZMod p) L (n : ZMod p)) x y := by
  rw [pulledEntry, TR.pullback_trace _ _ (signed_core_lisse K R G) L x y _ _
    (PhysicalTorusMorphism.schemePoint_physicalMorphism α m n x y),
    signed_core_parameter_trace K R T M]
  have hmap := PhysicalTorusMorphism.mappedParameters_value (K := ZMod p) α m n x y
  rw [hmap.1, hmap.2]
  exact FiniteFieldSums.signed_parabolicInputSum_eq_correctedKernel p _ _ _ _ _
    (by simpa only [map_zero] using (algebraMap (ZMod p) L).injective.ne α.ne_zero)
    (by simpa only [map_zero] using (algebraMap (ZMod p) L).injective.ne m.ne_zero)
    (by simpa only [map_zero] using (algebraMap (ZMod p) L).injective.ne n.ne_zero) x.ne_zero y.ne_zero

/-- The original cyclic four factors.  Conjugation uses dual(-1). -/
def entryObjects (α m m' n n' : (ZMod p)ˣ) : Fin 4 → C :=
  ![pulledEntry (H := H) (P := P) K O α m n, P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m' n),
    pulledEntry (H := H) (P := P) K O α m' n', P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m n')]

include R G TR in
theorem entryObjects_lisse (α m m' n n' : (ZMod p)ˣ) (i : Fin 4) :
    P.Lisse (entryObjects (H := H) (P := P) K O α m m' n n' i) := by
  fin_cases i
  · exact pulledEntry_lisse K R G O T TR _ _ _
  · exact G.dualTate_lisse _ (pulledEntry_lisse K R G O T TR _ _ _)
  · exact pulledEntry_lisse K R G O T TR _ _ _
  · exact G.dualTate_lisse _ (pulledEntry_lisse K R G O T TR _ _ _)

include R G TR in
theorem entryObjects_pure (α m m' n n' : (ZMod p)ˣ) (i : Fin 4) :
    P.Pure (entryObjects (H := H) (P := P) K O α m m' n n' i) 1 := by
  fin_cases i
  · exact pulledEntry_pure K R G O T TR _ _ _
  · change P.Pure (P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m' n)) 1
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      G.dualTate_pure _ 1 (pulledEntry_lisse K R G O T TR _ _ _)
        (pulledEntry_pure K R G O T TR _ _ _)
  · exact pulledEntry_pure K R G O T TR _ _ _
  · change P.Pure (P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m n')) 1
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      G.dualTate_pure _ 1 (pulledEntry_lisse K R G O T TR _ _ _)
        (pulledEntry_pure K R G O T TR _ _ _)

include R G TR M in
theorem entryObjects_trace (α m m' n n' : (ZMod p)ˣ) (L : Type) [Field L] [Fintype L]
    [Algebra (ZMod p) L] (x y : Lˣ) (i : Fin 4) :
    T.trace L (entryObjects (H := H) (P := P) K O α m m' n n' i) x y =
      FiniteFieldSums.extensionSign p L * FiniteFieldSums.correctedCycleFactors
        (FiniteFieldSums.traceAddChar p L) (algebraMap (ZMod p) L (α : ZMod p))
        (algebraMap (ZMod p) L (m : ZMod p)) (algebraMap (ZMod p) L (m' : ZMod p))
        (algebraMap (ZMod p) L (n : ZMod p)) (algebraMap (ZMod p) L (n' : ZMod p)) i x y := by
  fin_cases i
  · exact pulledEntry_trace K R G O T TR M _ _ _ L x y
  · change T.trace L (P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m' n)) x y = _
    rw [TR.dualTate_trace _ (pulledEntry_lisse K R G O T TR _ _ _)
      (pulledEntry_pure K R G O T TR _ _ _) L x y,
      pulledEntry_trace K R G O T TR M, ← FiniteFieldSums.extensionSign_mul_star]
    rfl
  · exact pulledEntry_trace K R G O T TR M _ _ _ L x y
  · change T.trace L (P.dualTateMinusOne (pulledEntry (H := H) (P := P) K O α m n')) x y = _
    rw [TR.dualTate_trace _ (pulledEntry_lisse K R G O T TR _ _ _)
      (pulledEntry_pure K R G O T TR _ _ _) L x y,
      pulledEntry_trace K R G O T TR M, ← FiniteFieldSums.extensionSign_mul_star]
    rfl

end PhysicalEntries

section TensorProducts

variable {C : Type w} [Category.{z} C] [MonoidalCategory C]

/-- A specified finite iterated tensor using the actual monoidal
product and tensor unit.  No new tensor-product object is postulated. -/
def tensorList (V : Fin 4 → C) (is : List (Fin 4)) : C :=
  is.foldr (fun i A => V i ⊗ A) (𝟙_ C)

/-- The same finite tensor at the canonical list of a finite subset. -/
def tensorSubset (V : Fin 4 → C) (S : Finset (Fin 4)) : C :=
  tensorList V S.toList

variable {p : ℕ} [Fact p.Prime] {P : ParameterData C}
  {O : TorusOperationData p C} {T : TorusArithmeticData p C}
  (TR : TorusRules P O T) (V : Fin 4 → C)

include TR

theorem tensorList_lisse (hV : ∀ i, P.Lisse (V i)) (is : List (Fin 4)) :
    P.Lisse (tensorList V is) := by
  induction is with
  | nil => exact TR.unit_lisse
  | cons i is ih => exact TR.tensor_lisse _ _ (hV i) ih

theorem tensorList_pure (hV : ∀ i, P.Pure (V i) 1) (is : List (Fin 4)) :
    P.Pure (tensorList V is) (is.length : ℝ) := by
  induction is with
  | nil => simpa only [tensorList, List.foldr_nil, List.length_nil, Nat.cast_zero] using TR.unit_pure
  | cons i is ih =>
      change P.Pure (V i ⊗ tensorList V is) ((is.length + 1 : ℕ) : ℝ)
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        TR.tensor_pure _ _ 1 (is.length : ℝ) (hV i) ih

theorem tensorList_trace (hV : ∀ i, P.Lisse (V i)) (is : List (Fin 4))
    (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L] (x y : Lˣ) :
    T.trace L (tensorList V is) x y = (is.map fun i => T.trace L (V i) x y).prod := by
  induction is with
  | nil => exact TR.unit_trace L x y
  | cons i is ih =>
      change T.trace L (V i ⊗ tensorList V is) x y = _
      rw [TR.tensor_trace _ _ (hV i) (tensorList_lisse TR V hV is), ih]
      rfl

theorem tensorSubset_lisse (hV : ∀ i, P.Lisse (V i)) (S : Finset (Fin 4)) :
    P.Lisse (tensorSubset V S) := tensorList_lisse TR V hV S.toList

theorem tensorSubset_pure (hV : ∀ i, P.Pure (V i) 1) (S : Finset (Fin 4)) :
    P.Pure (tensorSubset V S) (S.card : ℝ) := by
  simpa only [tensorSubset, Finset.length_toList] using tensorList_pure TR V hV S.toList

theorem tensorSubset_trace (hV : ∀ i, P.Lisse (V i)) (S : Finset (Fin 4))
    (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L] (x y : Lˣ) :
    T.trace L (tensorSubset V S) x y = ∏ i ∈ S, T.trace L (V i) x y := by
  rw [tensorSubset, tensorList_trace TR V hV, Finset.prod_map_toList]

end TensorProducts

open PublishedSupportRules PublishedStalkCertificate PublishedCovarianceRules

/-- Intermediate extension from the whole torus followed by shift [2],
with its geometric object and its chosen Weil lift kept separate. -/
structure IntermediateExtensionData {p : ℕ} [Fact p.Prime] {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    (realization : RationalStalkRealization p D) (C : Type w) where
  geometric : C → Obj
  weil : ∀ A, realization.WeilLift (geometric A)

/-- Generic intermediate-extension and tensor-trace laws on the fixed
smooth normal torus.  Sources are BBD 1.4.24--25, 4.3.1 and 5.3.2, and
Weil II 3.4.1(iii) for the geometric semisimplicity in `TorusIC`.
The shift is [2], so it adds two to weight and has positive trace sign. -/
structure IntermediateExtensionRules {p : ℕ} [Fact p.Prime] {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : RationalStalkRealization p D} {fourier : Obj → Obj}
    (W : TraceWeightRules p D realization fourier) (Z : TraceData p realization)
    {C : Type w} [Category.{z} C]
    (P : ParameterData C) (T : TorusArithmeticData p C)
    (IC : IntermediateExtensionData realization C) : Prop where
  pure : ∀ A a, P.Lisse A → P.Pure A a → W.PureOfWeight (IC.weil A) (a + 2)
  full : ∀ A a, P.Lisse A → P.Pure A a → D.NoProperConstituents (IC.geometric A)
  torusIC : ∀ A a, P.Lisse A → P.Pure A a → Z.TorusIC (IC.geometric A)
  trace : ∀ A, P.Lisse A →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : Lˣ,
      Z.trace L (IC.weil A) (x : L) (y : L) = T.trace L A x y

/-- The actual IC of the actual finite tensor. -/
def physicalObjects {p : ℕ} [Fact p.Prime] {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : RationalStalkRealization p D}
    {C : Type w} [Category.{z} C] [MonoidalCategory C]
    (IC : IntermediateExtensionData realization C) (V : Fin 4 → C)
    (S : Finset (Fin 4)) : Obj := IC.geometric (tensorSubset V S)

/-- The matching Weil lift, supplied by the same IC operation. -/
def physicalLift {p : ℕ} [Fact p.Prime] {Obj : Type u}
    {D : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
    {realization : RationalStalkRealization p D}
    {C : Type w} [Category.{z} C] [MonoidalCategory C]
    (IC : IntermediateExtensionData realization C) (V : Fin 4 → C)
    (S : Finset (Fin 4)) : realization.WeilLift (physicalObjects IC V S) :=
  IC.weil (tensorSubset V S)

section PhysicalIntermediateExtension

universe a

variable {p : ℕ} [Fact p.Prime]
  {Input : Type u} {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C] [MonoidalCategory C]
  {D : CurveData Input Point} {H : CohomologyData Input C} {P : ParameterData C}
  (K : KloostermanInputData D) (R : CurveRules D) (G : CohomologyRules D H P)
  (O : TorusOperationData p C) (T : TorusArithmeticData p C)
  (TR : TorusRules P O T) (M : CohomologicalRealization D H P K T)
  {Obj : Type a} {SD : SurfaceData (AlgebraicClosure (ZMod p)) Obj}
  {realization : RationalStalkRealization p SD} {fourier : Obj → Obj}
  (W : TraceWeightRules p SD realization fourier) (Z : TraceData p realization)
  (IC : IntermediateExtensionData realization C) (IR : IntermediateExtensionRules W Z P T IC)

include R G TR IR

/-- The requested physical weight follows from the constructed
weight-one entries, actual tensor and generic IC shift rule. -/
theorem physical_pure_weight (α m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    W.PureOfWeight (physicalLift IC (entryObjects (H := H) (P := P) K O α m m' n n') S)
      ((S.card : ℝ) + 2) :=
  IR.pure _ _
    (tensorSubset_lisse TR _ (entryObjects_lisse K R G O T TR α m m' n n') S)
    (tensorSubset_pure TR _ (entryObjects_pure K R G O T TR α m m' n n') S)

/-- Full support of every geometric constituent is an IC deduction,
not an input about this family. -/
theorem physical_full_constituents (α m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    SD.NoProperConstituents
      (physicalObjects IC (entryObjects (H := H) (P := P) K O α m m' n n') S) :=
  IR.full _ (S.card : ℝ)
    (tensorSubset_lisse TR _ (entryObjects_lisse K R G O T TR α m m' n n') S)
    (tensorSubset_pure TR _ (entryObjects_pure K R G O T TR α m m' n n') S)

/-- Geometric semisimplicity on the normal torus and IC uniqueness give
the geometric property needed by the corrected Chebotarev interface. -/
theorem physical_torusIC (α m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    Z.TorusIC (physicalObjects IC (entryObjects (H := H) (P := P) K O α m m' n n') S) :=
  IR.torusIC _ (S.card : ℝ)
    (tensorSubset_lisse TR _ (entryObjects_lisse K R G O T TR α m m' n n') S)
    (tensorSubset_pure TR _ (entryObjects_pure K R G O T TR α m m' n n') S)

include M in
/-- The all-extension expected trace is derived for the SAME Weil lift
as the rational stalk certificate.  Its exact (-1)^(d+1) factor appears
once for each selected entry, including both conjugated positions. -/
theorem physical_expectedTrace (α m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4)) :
    ExpectedCoreTrace Z
      (physicalLift IC (entryObjects (H := H) (P := P) K O α m m' n n') S)
      (α : ZMod p) (m : ZMod p) (m' : ZMod p) (n : ZMod p) (n' : ZMod p) S := by
  intro L _ _ _ x y hx hy
  let ux : Lˣ := Units.mk0 x hx
  let uy : Lˣ := Units.mk0 y hy
  change Z.trace L (IC.weil (tensorSubset
    (entryObjects (H := H) (P := P) K O α m m' n n') S)) (ux : L) (uy : L) = _
  rw [IR.trace _ (tensorSubset_lisse TR _ (entryObjects_lisse K R G O T TR α m m' n n') S),
    tensorSubset_trace TR _ (entryObjects_lisse K R G O T TR α m m' n n')]
  unfold FiniteFieldSums.expectedTrace
  apply Finset.prod_congr rfl
  intro i _
  exact entryObjects_trace K R G O T TR M α m m' n n' L ux uy i

include M in
/-- The prime-field trace field of FamilyConstruction follows from its
all-extension counterpart and the same-lift compatibility already proved
in the corrected covariance interface. -/
theorem physical_trace_on_units (α m m' n n' : (ZMod p)ˣ) (S : Finset (Fin 4))
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) :
    (realization.stalk
      (physicalLift IC (entryObjects (H := H) (P := P) K O α m m' n n') S) x y).trace =
        ∏ i ∈ S, correctedCycleFactors p α m m' n n' i x y :=
  trace_on_units_of_expected_core_trace Z _ _ _ _ _ _ _
    (physical_expectedTrace K R G O T TR M W Z IC IR α m m' n n' S) x y hx hy

end PhysicalIntermediateExtension

end PrimeGap182.TypeIII.PublishedPhysicalConstruction

-- Axiom audit

#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.tensor
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.dual
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.Lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.Pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.TameZero
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.BreaksLE
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.Isoclinic
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.swanZero
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveData.swanInfinity
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tensor_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tensor_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tensor_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.dual_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.dual_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.dual_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tensor_tame
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.dual_tame
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tensor_breaks
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.dual_breaks
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tensor_unequal_breaks
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.dual_isoclinic
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.tame_swan
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveRules.slope_one_swan
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.first
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.second
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.additive
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.first_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.second_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.additive_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.first_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.second_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.additive_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.first_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.second_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.additive_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.first_tame
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.second_tame
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.additive_tame
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.first_breaks
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.second_breaks
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.additive_slope
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_tame
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_slope_one
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_swan
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.dual_input_swan
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.input_conductor
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanInputData.dual_input_conductor
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.compact
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.ordinary
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyData.comparison
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.Lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.Pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.dualTateMinusOne
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ParameterData.signed
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.parabolicCore
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.compact_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.ordinary_duality
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.dualTate_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.lisse_of_iso
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.image_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.image_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.signed_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.signed_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologyRules.dualTate_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.compact_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.compact_dual_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.ordinary_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.core_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.core_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.signed_core_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.signed_core_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.conjugate_signed_core_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalkImageIso
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalkQuotient
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalkInclusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalkQuotient_surjective
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalkInclusion_injective
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalk_factorization
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.coreStalkQuotient_ker
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.boundary
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.injective
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.exact
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.frobenius
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.OriginBoundaryModel.jordanData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.point
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveTraceData.trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.compact_finite
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.compact_rank
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.compact_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.tensor_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CurveFiberRules.dual_weight_zero_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.first_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.second_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanTraceData.additive_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.compact_rank_nine
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.input_point_sum
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.compact_trace_input_sum
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.core_stalk_rank_six
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.core_stalk_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.signed_core_stalk_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.space
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.toCompact
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyData.frobenius
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.injective
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.exact
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.BoundaryCohomologyRules.frobenius
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.identification
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.KloostermanBoundaryData.frobenius
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.originBoundaryModel
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.comparison
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.frobenius
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.SignStalkComparison.trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.signed_sheaf_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.signed_sheaf_kernel_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.fiber
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.frobenius
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.finite
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusArithmeticData.trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusOperationData.pullback
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.pullback_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.pullback_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.unit_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.unit_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.tensor_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.tensor_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.unit_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.tensor_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.dualTate_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.TorusRules.pullback_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.additive
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.finiteLimits
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.finiteColimits
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.curveTrace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.fiberRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.originalTraces
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.boundary
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.boundaryRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.localBoundary
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.CohomologicalRealization.sign
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.signed_core_parameter_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.pulledEntry
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.pulledEntry_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.pulledEntry_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.pulledEntry_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.entryObjects
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.entryObjects_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.entryObjects_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.entryObjects_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorList
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorSubset
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorList_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorList_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorList_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorSubset_lisse
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorSubset_pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.tensorSubset_trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.geometric
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionData.weil
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.rec
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.pure
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.full
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.torusIC
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.IntermediateExtensionRules.trace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physicalObjects
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physicalLift
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physical_pure_weight
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physical_full_constituents
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physical_torusIC
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physical_expectedTrace
#print axioms PrimeGap182.TypeIII.PublishedPhysicalConstruction.physical_trace_on_units
