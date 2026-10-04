import TypeIIIImageWeightsFromCompact
import TypeIIIConstantSignFromStalks

/-!
# Parameter purity defined on the original rational-point Frobenius

Use the fixed-embedding pointwise weight convention of Weil II 1.2.6,
on all actual rational points over finite extensions. The forward and
reflection interfaces are the two directions of this definition, not
additional theorem assumptions. The existing lisse dual/Tate spectral
law then proves purity of weight 2-a for the original dual(-1) functor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.ParameterPurityFromStalks
open SourceInverseImageSystem RationalPointStalks PublishedPhysicalConstruction

universe mu
variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)} (R : Data B)

/-- Fixed-embedding pointwise purity, on the same original characteristic roots. -/
def pointwisePure (X : Space (ZMod p)) (A : B.Obj X) (a : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X),
    ∀ z ∈ PureDualTrace.eigenvalues R E X x A,
      Complex.normSq z = (Fintype.card E : ℝ) ^ a

theorem weights (X : Space (ZMod p)) : PureDualTrace.Weights R X (pointwisePure R X) where
  weight E _ _ _ x _ _ h := h E x

theorem reflection (X : Space (ZMod p)) :
    PointImagePurity.PurityReflection R X (pointwisePure R X) where
  pure _ _ h := h

/-- Choose parameter purity from the stalks; only lissity remains an observable. -/
def parameterGeometry (Lisse : B.Obj .torus → Prop) :
    ConstantSignFromStalks.ParameterGeometry (B.Obj .torus) where
  Lisse := Lisse
  Pure := pointwisePure R .torus

/-- Pullback purity uses the actual point comparison and original Frobenius. -/
theorem pullback_pure {X Y : Space (ZMod p)}
    (f : scheme (ZMod p) X ⟶ scheme (ZMod p) Y) (A : B.Obj Y) (a : ℝ)
    (hp : pointwisePure R Y A a) : pointwisePure R X ((B.pull f).obj A) a := by
  intro E _ _ _ x z hz
  let := R.finite E X x ((B.pull f).obj A)
  let := R.finite E Y (x ≫ f) A
  let e := ((R.pullback E f x).app A).toLinearEquiv
  have hn (v) : e (((R.frobenius E X x).app ((B.pull f).obj A)).hom v) =
      ((R.frobenius E Y (x ≫ f)).app A).hom (e v) :=
    congrArg (fun m => m.hom v) (R.frobenius_pullback E f x A)
  exact hp E (x ≫ f) z (ImageWeightsFromCompact.roots_of_injective
    ((R.frobenius E X x).app ((B.pull f).obj A)).hom
    ((R.frobenius E Y (x ≫ f)).app A).hom e.toLinearMap e.injective hn hz)

/-- The same monoidal unit comparison has identity Frobenius and weight zero. -/
theorem unit_pure (T : PointTraceFromTensor.Laws R) (X : Space (ZMod p)) :
    pointwisePure R X (𝟙_ (B.Obj X)) 0 := by
  intro E _ _ _ x z hz
  let stalkMonoidal := T.monoidal E X x
  let := R.finite E X x (𝟙_ (B.Obj X))
  let e := (Functor.Monoidal.εIso (R.fiber E X x)).toLinearEquiv.symm
  have hn (v) : e (((R.frobenius E X x).app (𝟙_ (B.Obj X))).hom v) =
      (1 : ℂ →ₗ[ℂ] ℂ) (e v) := by
    have h := congrArg e (T.unit E X x (e v))
    simpa only [e, stalkMonoidal, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply, Module.End.one_apply] using h
  have hz' := ImageWeightsFromCompact.roots_of_injective
    ((R.frobenius E X x).app (𝟙_ (B.Obj X))).hom (1 : ℂ →ₗ[ℂ] ℂ)
    e.toLinearMap e.injective hn hz
  have heq : z = 1 := by
    simpa [LinearMap.charpoly_one, Module.finrank_self, Polynomial.IsRoot, sub_eq_zero] using
      (Polynomial.mem_roots (LinearMap.charpoly_monic (1 : ℂ →ₗ[ℂ] ℂ)).ne_zero).mp hz'
  rw [heq]
  simp

theorem dual_weight {q : ℝ} (hq : 0 < q) (a : ℝ) {t : ℂ}
    (hw : Complex.normSq t = q ^ a) :
    Complex.normSq ((q : ℂ) / t) = q ^ (2 - a) := by
  rw [Complex.normSq_div, Complex.normSq_ofReal, hw, Real.rpow_sub hq,
    Real.rpow_two]
  ring

variable {R} {X : Space (ZMod p)} {Lisse : B.Obj X → Prop}
  {DT : (B.Obj X)ᵒᵖ ⥤ B.Obj X}

/-- Apply the original dual(-1) spectral law at every finite rational point. -/
theorem dualTate_pure (DS : PureDualTrace.DualSpectrum R X DT Lisse 1)
    (A : B.Obj X) (a : ℝ) (hl : Lisse A) (hp : pointwisePure R X A a) :
    pointwisePure R X (DT.obj (Opposite.op A)) (2 - a) := by
  intro E _ _ _ x z hz
  rw [DS.roots E x A hl] at hz
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hz
  have hq : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  simpa only [pow_one, Complex.ofReal_natCast] using dual_weight hq a (hp E x t ht)

/-- Retain the three lissity laws and tensor purity; pullback and unit
purity are proved from the common point-stalk system. -/
structure TorusRules (P : ParameterData (B.Obj .torus)) : Prop where
  pullback_lisse : ∀ f A, P.Lisse A → P.Lisse ((B.torusOperations.pullback f).obj A)
  unit_lisse : P.Lisse (𝟙_ (B.Obj .torus))
  tensor_lisse : ∀ A C, P.Lisse A → P.Lisse C → P.Lisse (A ⊗ C)
  tensor_pure : ∀ A C a b, P.Pure A a → P.Pure C b → P.Pure (A ⊗ C) (a + b)

/-- The five unchanged physical laws, excluding the now-derived dual purity. -/
structure OtherRules (P : ParameterData (B.Obj .torus)) : Prop where
  dualTate_lisse : ∀ A, P.Lisse A → P.Lisse (P.dualTateMinusOne A)
  lisse_of_iso : ∀ A C, Nonempty (A ≅ C) → P.Lisse C → P.Lisse A
  image_lisse : ∀ A C (f : A ⟶ C), P.Lisse A → P.Lisse C → P.Lisse (Abelian.image f)
  signed_lisse : ∀ A, P.Lisse A → P.Lisse (P.signed A)
  signed_pure : ∀ A a, P.Pure A a → P.Pure (P.signed A) a

variable (R) (L : B.Obj .torus → Prop) (line : B.Obj .torus)
  (dual : (B.Obj .torus)ᵒᵖ ⥤ B.Obj .torus)

theorem torusGeometry (T : PointTraceFromTensor.Laws R)
    (G : TorusRules (((parameterGeometry R L).withLine line).data dual)) :
    PureDualTrace.TorusGeometry (((parameterGeometry R L).withLine line).data dual) where
  pullback_lisse := G.pullback_lisse
  pullback_pure := pullback_pure R (X := .torus) (Y := .torus)
  unit_lisse := G.unit_lisse
  unit_pure := unit_pure R T .torus
  tensor_lisse := G.tensor_lisse
  tensor_pure := G.tensor_pure

/-- Construct the remaining physical interface on the selected purity predicate. -/
theorem physicalOtherRules (DS : PureDualTrace.DualSpectrum R .torus dual L 1)
    (G : OtherRules (((parameterGeometry R L).withLine line).data dual)) :
    PointImagePurity.OtherRules (((parameterGeometry R L).withLine line).data dual) where
  dualTate_lisse := G.dualTate_lisse
  lisse_of_iso := G.lisse_of_iso
  image_lisse := G.image_lisse
  signed_lisse := G.signed_lisse
  signed_pure := G.signed_pure
  dualTate_pure := dualTate_pure DS

end PrimeGap182.TypeIII.ParameterPurityFromStalks

#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.pointwisePure
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.weights
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.reflection
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.parameterGeometry
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.pullback_pure
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.unit_pure
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.dual_weight
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.dualTate_pure
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.torusGeometry
#print axioms PrimeGap182.TypeIII.ParameterPurityFromStalks.physicalOtherRules
