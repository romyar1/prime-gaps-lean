import TypeIIIBoundaryFromSourceModels
import Mathlib.Algebra.Homology.SingleHomology

/-!
# The actual middle-cohomology comparison from localization

Apply the two compact-support localization sequences for Gm inside A1
and A1 inside P1, then the degree-one Leray edge map for Gm inside P1.
The geometric-point cohomology is represented by the single complex in
degree zero. Its degree-one cohomology vanishes by Mathlib's homology
calculation. Positive slope removes the infinity-invariant source.

The general localization/Leray laws remain explicit geometric inputs.
No family boundary factorization, vanishing map, or image isomorphism is
assumed. References: Milne, Lectures on Etale Cohomology, Theorem 12.7,
Proposition 18.3(a), and the geometric-point calculation in section 9.
https://www.jmilne.org/math/CourseNotes/LEC.pdf
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace PrimeGap182.TypeIII.MiddleFromLocalization

open PublishedPhysicalConstruction BoundaryFromSourceModels
open ParabolicMiddleComparison GeometricCoreRank RegularUnipotentBoundary

universe u v w z a b c

/-- A geometric-point sheaf is a vector space in degree zero. -/
def pointH1 (V : ModuleCat.{w} ℂ) : ModuleCat.{w} ℂ :=
  ((HomologicalComplex.single (ModuleCat.{w} ℂ) (ComplexShape.up ℤ) 0).obj V).homology 1

theorem pointH1_isZero (V : ModuleCat.{w} ℂ) : IsZero (pointH1 V) :=
  HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 V 1 (by decide)

/-- Only a universe lift is used to put a boundary stalk in the same
module category as the cohomology objects. -/
def invariantModule {G : Type a} [Group G] (W : FDRep ℂ G) : ModuleCat.{w} ℂ :=
  ModuleCat.of ℂ (ULift.{w} (Representation.invariants W.ρ))

theorem invariantModule_isZero {G : Type a} [Group G] (W : FDRep ℂ G)
    (h : Representation.invariants W.ρ = ⊥) : IsZero (invariantModule.{w} W) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply ULift.ext
  apply Subtype.ext
  have hz : ∀ t : Representation.invariants W.ρ, t.val = 0 := by
    intro t
    apply (Submodule.mem_bot ℂ).mp
    rw [← h]
    exact t.property
  have hx := hz x.down
  have hy := hz y.down
  exact hx.trans hy.symm

variable {Input : Type u} [Category.{c} Input] {Point : Type v} {C : Type w}
  [Category.{z} C] [Abelian C]
  {D : CurveData Input Point} {H : CohomologyData Input C}
  {F : C ⥤ ModuleCat.{w} ℂ} {S : BoundarySequence D H F}
  {G0 : Type a} [Group G0] {Ginf : Type b} [Group Ginf]
  (Z : RestrictionData (G0 := G0) (Ginf := Ginf) D H F S)

/-- Cohomology and the natural maps for ordinary extensions of every
lisse curve input. `affine` is Hc1(A1,j0_* A), `projective` is
H1(P1,jbar_* A). Both are functors so later source isomorphisms act on
these same cohomology objects. -/
structure CompactificationData where
  affine : Input ⥤ ModuleCat.{w} ℂ
  projective : Input ⥤ ModuleCat.{w} ℂ
  fromCompact : ∀ A, F.obj (H.compact A) ⟶ affine.obj A
  toProjective : ∀ A, affine.obj A ⟶ projective.obj A
  leray : ∀ A, projective.obj A ⟶ F.obj (H.ordinary A)
  fromInfinity : ∀ A, invariantModule.{w} (Z.infinity A) ⟶ affine.obj A
  toZero : ∀ A, affine.obj A ⟶ pointH1 (invariantModule.{w} (Z.zero A))

variable (M : CompactificationData Z)

/-- General localization exactness, the degree-one Leray injection, and
compatibility with the original compact-to-ordinary map. The laws
quantify over arbitrary lisse inputs and specify no special family rank. -/
structure CompactificationRules : Prop where
  comparison : ∀ A, D.Lisse A →
    M.fromCompact A ≫ M.toProjective A ≫ M.leray A = F.map (H.comparison A)
  zero_exact : ∀ A, D.Lisse A →
    LinearMap.range (M.fromCompact A).hom = LinearMap.ker (M.toZero A).hom
  infinity_exact : ∀ A, D.Lisse A →
    LinearMap.range (M.fromInfinity A).hom = LinearMap.ker (M.toProjective A).hom
  leray_injective : ∀ A, D.Lisse A → Function.Injective (M.leray A).hom

variable (R : CompactificationRules Z M)

/-- Construct the previous comparison criterion from the two different
localization sequences, composing with the injective Leray edge map. -/
def boundaryFactorization (A : Input) (hA : D.Lisse A) :
    BoundaryFactorization (F.map (H.comparison A)) where
  middle := M.affine.obj A
  leftBoundary := invariantModule (Z.infinity A)
  rightBoundary := pointH1 (invariantModule (Z.zero A))
  fromCompact := M.fromCompact A
  toOrdinary := M.toProjective A ≫ M.leray A
  fromBoundary := M.fromInfinity A
  toBoundary := M.toZero A
  factorization := R.comparison A hA
  left_exact := by
    change LinearMap.range (M.fromInfinity A).hom =
      LinearMap.ker ((M.leray A).hom.comp (M.toProjective A).hom)
    rw [LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr (R.leray_injective A hA))]
    exact R.infinity_exact A hA
  right_exact := R.zero_exact A hA

omit [Abelian C] in
/-- The outgoing boundary map vanishes by the actual single-complex
calculation, rather than by a family-specific vanishing premise. -/
theorem toZero_eq_zero (A : Input) : (M.toZero A).hom = 0 := by
  have h := (pointH1_isZero (invariantModule (Z.zero A))).eq_of_tgt (M.toZero A) 0
  exact congrArg (fun f => f.hom) h

omit [Abelian C] in
/-- Positive slope kills the source of the incoming boundary map. -/
theorem fromInfinity_eq_zero (A : Input) (hA : D.Isoclinic A 1) :
    (M.fromInfinity A).hom = 0 := by
  have h := (invariantModule_isZero (Z.infinity A) (Z.positiveSlope A hA)).eq_of_src
    (M.fromInfinity A) 0
  exact congrArg (fun f => f.hom) h

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original parabolic stalk is the affine middle cohomology, with
both boundary vanishings derived from the general laws. -/
def coreStalkAffineIso (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1) :
    F.obj (parabolicCore H A) ≅ M.affine.obj A :=
  coreStalkMiddleIso H F A (boundaryFactorization Z M R A hA)
    (fromInfinity_eq_zero Z M A hs) (toZero_eq_zero Z M A)

theorem coreStalkAffineIso_toOrdinary (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1) :
    (coreStalkAffineIso Z M R A hA hs).hom ≫ M.toProjective A ≫ M.leray A =
      F.map (Abelian.image.ι (H.comparison A)) :=
  coreStalkMiddleIso_hom_toOrdinary H F A (boundaryFactorization Z M R A hA)
    (fromInfinity_eq_zero Z M A hs) (toZero_eq_zero Z M A)

theorem fromCompact_coreStalkAffineIso (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1) :
    F.map (Abelian.factorThruImage (H.comparison A)) ≫ (coreStalkAffineIso Z M R A hA hs).hom =
      M.fromCompact A :=
  fromCompact_coreStalkMiddleIso_hom H F A (boundaryFactorization Z M R A hA)
    (fromInfinity_eq_zero Z M A hs) (toZero_eq_zero Z M A)

theorem coreStalkAffineIso_natural (A : Input) (hA : D.Lisse A) (hs : D.Isoclinic A 1)
    (a : F.obj (H.compact A) ⟶ F.obj (H.compact A))
    (b : F.obj (parabolicCore H A) ⟶ F.obj (parabolicCore H A))
    (c : M.affine.obj A ⟶ M.affine.obj A)
    (hab : a ≫ F.map (Abelian.factorThruImage (H.comparison A)) =
      F.map (Abelian.factorThruImage (H.comparison A)) ≫ b)
    (hac : a ≫ M.fromCompact A = M.fromCompact A ≫ c) :
    b ≫ (coreStalkAffineIso Z M R A hA hs).hom = (coreStalkAffineIso Z M R A hA hs).hom ≫ c :=
  coreStalkMiddleIso_natural H F A (boundaryFactorization Z M R A hA)
    (fromInfinity_eq_zero Z M A hs) (toZero_eq_zero Z M A) a b c hab hac

include R in
/-- Rank six for the actual affine middle cohomology, using the already
constructed geometric boundary from individual regular-unipotent sources. -/
theorem affine_rank_six (K : KloostermanInputData D) (CR : CurveRules D)
    {rho : Representation ℂ G0 (Fin 3 → ℂ)} (U : RegularModel rho)
    (hfirst : Representation.Equiv (Z.zero K.first).ρ rho)
    (hsecond : Representation.Equiv (Z.zero K.second).ρ rho)
    (hadditive : Representation.Equiv (Z.zero K.additive).ρ (Representation.trivial ℂ G0 ℂ))
    (point : Point) (V : GeometricFiberRules D H F point) :
    Module.finrank ℂ (M.affine.obj K.input) = 6 := by
  rw [← (coreStalkAffineIso Z M R K.input (K.input_lisse CR)
    (K.input_slope_one CR)).toLinearEquiv.finrank_eq]
  exact core_rank_six_from_sources Z K CR U hfirst hsecond hadditive point V

end PrimeGap182.TypeIII.MiddleFromLocalization

#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.pointH1_isZero
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.invariantModule_isZero
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.boundaryFactorization
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.toZero_eq_zero
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.fromInfinity_eq_zero
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.coreStalkAffineIso
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.coreStalkAffineIso_toOrdinary
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.fromCompact_coreStalkAffineIso
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.coreStalkAffineIso_natural
#print axioms PrimeGap182.TypeIII.MiddleFromLocalization.affine_rank_six
