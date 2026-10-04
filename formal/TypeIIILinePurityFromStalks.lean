import TypeIIISourcePurityFromStalks

/-!
# Primitive purity on units and its actual scalar pullbacks

Primitive Kloosterman purity is required on Gm, not at the affine origin.
Every finite-field point of the actual relative source maps to a unit
under each parameter-unit scalar map. The same point-stalk comparison
therefore transfers primitive purity to the source, without a separate
scalar-pullback purity law or an origin-purity premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace PrimeGap182.TypeIII.LinePurityFromStalks
open StartingSourceMaps StartingSourceComplexity CanonicalCurveInput SourceInverseImageSystem RationalPointStalks
open PublishedPhysicalConstruction ParameterPurityFromStalks

universe mu u v w

/-- The five unchanged primitive geometric observables. -/
structure Observables (C : Type u) where
  LisseOnUnits : C → Prop
  rank : C → ℕ
  TameZero : C → Prop
  BreaksLE : C → ℚ → Prop
  Isoclinic : C → ℚ → Prop

variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)}
  (R : Data B)

/-- The primitive weight condition at the original nonzero line points. -/
def pureOnUnits (A : B.Obj .line) (a : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (x : Eˣ),
    ∀ z ∈ PureDualTrace.eigenvalues R E .line (linePoint (x : E)) A,
      Complex.normSq z = (Fintype.card E : ℝ) ^ a

def geometry (O : Observables (B.Obj .line)) : LineGeometry (B.Obj .line) where
  LisseOnUnits := O.LisseOnUnits
  rank := O.rank
  Pure := pureOnUnits R
  TameZero := O.TameZero
  BreaksLE := O.BreaksLE
  Isoclinic := O.Isoclinic

/-- A parameter unit times the invertible curve coordinate is still a
unit at every source point. This statement uses the original scheme map. -/
theorem scalar_point (E : Type) [Field E] [Algebra (ZMod p) E]
    (c : (PhysicalTorusMorphism.TorusRing (ZMod p))ˣ)
    (x : Spec (.of E) ⟶ sourceScheme (ZMod p)) :
    ∃ z : Eˣ, x ≫ scalarMorphism (ZMod p) c = linePoint (z : E) := by
  let f := (Spec.preimage x).hom
  have hc : f.comp (algebraMap (ZMod p) (SourceRing (ZMod p))) = algebraMap (ZMod p) E :=
    Subsingleton.elim _ _
  let a : SourceRing (ZMod p) →ₐ[ZMod p] E :=
    { f with commutes' := fun t => congrArg (fun m => m t) hc }
  let z : Eˣ := Units.map a.toRingHom
    (Units.map (parameterHom (ZMod p)).toRingHom c * coordinateUnit (ZMod p) 0)
  have he : a.comp (scalarHom (ZMod p) c) = aeval (fun _ : Fin 1 => (z : E)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, scalarHom, aeval_X]
    rfl
  refine ⟨z, ?_⟩
  have hx : x = Spec.map (CommRingCat.ofHom a.toRingHom) := (Spec.map_preimage x).symm
  rw [hx]
  dsimp only [scalarMorphism, linePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun m => Spec.map (CommRingCat.ofHom m)) (congrArg AlgHom.toRingHom he)

/-- Scalar pullback preserves primitive purity because its point image
lies on Gm and the actual Frobenius operators are intertwined. -/
theorem scalar_pure (c : (PhysicalTorusMorphism.TorusRing (ZMod p))ˣ)
    (A : B.Obj .line) (a : ℝ) (hp : pureOnUnits R A a) :
    pointwisePure R .source ((B.pull (X := .source) (Y := .line) (scalarMorphism (ZMod p) c)).obj A) a := by
  intro E _ _ _ x z hz
  let f := scalarMorphism (ZMod p) c
  let := R.finite E .source x ((B.pull (X := .source) (Y := .line) f).obj A)
  let := R.finite E .line (x ≫ f) A
  let e := ((R.pullback E (X := .source) (Y := .line) f x).app A).toLinearEquiv
  have hn (v) : e (((R.frobenius E .source x).app ((B.pull (X := .source) (Y := .line) f).obj A)).hom v) =
      ((R.frobenius E .line (x ≫ f)).app A).hom (e v) :=
    congrArg (fun m => m.hom v) (R.frobenius_pullback E (X := .source) (Y := .line) f x A)
  have hz' := ImageWeightsFromCompact.roots_of_injective
    ((R.frobenius E .source x).app ((B.pull (X := .source) (Y := .line) f).obj A)).hom
    ((R.frobenius E .line (x ≫ f)).app A).hom e.toLinearMap e.injective hn hz
  change z ∈ PureDualTrace.eigenvalues R E .line (x ≫ scalarMorphism (ZMod p) c) A at hz'
  obtain ⟨u, hu⟩ := scalar_point E c x
  rw [hu] at hz'
  exact hp E u z hz'

/-- The five retained scalar pullback rules, with purity removed. -/
structure GeometricPullbackRules {k : Type} [Field k]
    {LineObj : Type u} {Input : Type v} {Point : Type w}
    (F : PullbackData k LineObj Input) (L : LineGeometry LineObj)
    (D : CurveData Input Point) : Prop where
  lisse : ∀ c A, L.LisseOnUnits A → D.Lisse (F.pullback (scalarMorphism k c) A)
  rank : ∀ c A, L.LisseOnUnits A → D.rank (F.pullback (scalarMorphism k c) A) = L.rank A
  tame : ∀ c A, L.TameZero A → D.TameZero (F.pullback (scalarMorphism k c) A)
  breaks : ∀ c A s, L.BreaksLE A s → D.BreaksLE (F.pullback (scalarMorphism k c) A) s
  isoclinic : ∀ c A s, L.Isoclinic A s → D.Isoclinic (F.pullback (scalarMorphism k c) A) s

variable {Point : Type w} (O : Observables (B.Obj .line))
  (S : SourcePurityFromStalks.Observables (B.Obj .source) Point)
  (dual : (B.Obj .source)ᵒᵖ ⥤ B.Obj .source)

/-- The old scalar interface now uses the proved purity transport on
the same source and line functors; other geometric clauses are unchanged. -/
theorem scalarRules
    (G : GeometricPullbackRules (FourierSourcePullbacks.originalPullbackData (ZMod p) B.geometricPullbacks)
      (geometry R O) ((SourcePurityFromStalks.geometry R S).curveData dual)) :
    ScalarPullbackRules (FourierSourcePullbacks.originalPullbackData (ZMod p) B.geometricPullbacks)
      (geometry R O) ((SourcePurityFromStalks.geometry R S).curveData dual) where
  lisse := G.lisse
  rank := G.rank
  pure := scalar_pure R
  tame := G.tame
  breaks := G.breaks
  isoclinic := G.isoclinic

end PrimeGap182.TypeIII.LinePurityFromStalks

#print axioms PrimeGap182.TypeIII.LinePurityFromStalks.pureOnUnits
#print axioms PrimeGap182.TypeIII.LinePurityFromStalks.geometry
#print axioms PrimeGap182.TypeIII.LinePurityFromStalks.scalar_point
#print axioms PrimeGap182.TypeIII.LinePurityFromStalks.scalar_pure
#print axioms PrimeGap182.TypeIII.LinePurityFromStalks.scalarRules
