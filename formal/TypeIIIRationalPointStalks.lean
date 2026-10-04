import TypeIIISourceInverseImageSystem
import TypeIIICanonicalInputTrace
import TypeIIIPublishedPrimitiveSources

/-!
# One rational-point stalk system for line, curve and torus traces

General pullback/stalk comparison commutes with geometric Frobenius.
The resulting trace identity is derived by conjugation of the actual
operators. Line, curve and torus traces use this same system. The curve
coordinate formula is proved for every algebraic map to the affine line.
Laumon 1.1.1.4 is the corresponding general trace-function identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.RationalPointStalks
open SourceInverseImageSystem StartingSourceMaps PublishedPhysicalConstruction
open CanonicalInputTrace CanonicalCurveInput GenericCurvePullback FourierSourcePullbacks

universe mu h
variable {p : ℕ} [Fact p.Prime] (B : System.{0,mu} (ZMod p))

/-- General finite arithmetic stalks on the actual indexed schemes.
The comparison and Frobenius equation hold before any source is chosen. -/
structure Data where
  fiber : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (X : Space (ZMod p)),
    (Spec (.of E) ⟶ scheme (ZMod p) X) → B.Obj X ⥤ ModuleCat.{0} ℂ
  frobenius : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x,
    fiber E X x ⟶ fiber E X x
  finite : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x A,
    FiniteDimensional ℂ ((fiber E X x).obj A)
  pullback : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] {X Y}
    (f : scheme (ZMod p) X ⟶ scheme (ZMod p) Y) (x : Spec (.of E) ⟶ scheme (ZMod p) X),
    B.pull f ⋙ fiber E X x ≅ fiber E Y (x ≫ f)
  frobenius_pullback : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] {X Y}
    (f : scheme (ZMod p) X ⟶ scheme (ZMod p) Y) (x : Spec (.of E) ⟶ scheme (ZMod p) X) A,
    (frobenius E X x).app ((B.pull f).obj A) ≫ (pullback E f x).hom.app A =
      (pullback E f x).hom.app A ≫ (frobenius E Y (x ≫ f)).app A

variable {B} (R : Data B)
  (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]

def Data.trace {X : Space (ZMod p)} (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj X) : ℂ :=
  LinearMap.trace ℂ ((R.fiber E X x).obj A) ((R.frobenius E X x).app A).hom

/-- Conjugacy through the actual stalk comparison gives trace pullback. -/
theorem Data.pullback_trace {X Y : Space (ZMod p)}
    (f : scheme (ZMod p) X ⟶ scheme (ZMod p) Y)
    (x : Spec (.of E) ⟶ scheme (ZMod p) X) (A : B.Obj Y) :
    R.trace E x ((B.pull f).obj A) = R.trace E (x ≫ f) A := by
  let e := (R.pullback E f x).app A
  have hn (v) : e.toLinearEquiv (((R.frobenius E X x).app ((B.pull f).obj A)).hom v) =
      ((R.frobenius E Y (x ≫ f)).app A).hom (e.toLinearEquiv v) :=
    congrArg (fun m => m.hom v) (R.frobenius_pullback E f x A)
  have hc : e.toLinearEquiv.conj (((R.frobenius E X x).app ((B.pull f).obj A)).hom) =
      ((R.frobenius E Y (x ≫ f)).app A).hom := by
    ext v
    change e.toLinearEquiv (((R.frobenius E X x).app ((B.pull f).obj A)).hom
      (e.toLinearEquiv.symm v)) = _
    rw [hn, e.toLinearEquiv.apply_symm_apply]
  exact (LinearMap.trace_conj' _ e.toLinearEquiv).symm.trans (congrArg (LinearMap.trace ℂ _) hc)

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The actual rational point of the original affine line, including zero. -/
def linePoint (z : L) : Spec (.of L) ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (aeval (R := K) (fun _ : Fin 1 => z)).toRingHom)

/-- The actual point of the source Gm cubed, with all three coordinates. -/
def curvePoint (x lambda xi : Lˣ) : Spec (.of L) ⟶ sourceScheme K :=
  Spec.map (CommRingCat.ofHom (evaluation (K := K) x lambda xi).toRingHom)

/-- Composition with any affine-line map is its original coordinate evaluation. -/
theorem curvePoint_comp (g : MvPolynomial (Fin 1) K →ₐ[K] SourceRing K) (x lambda xi : Lˣ) :
    curvePoint x lambda xi ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
      linePoint (evaluation (K := K) x lambda xi (g (X 0))) := by
  have h : (evaluation (K := K) x lambda xi).comp g =
      aeval (fun _ : Fin 1 => evaluation (K := K) x lambda xi (g (X 0))) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  dsimp only [curvePoint, linePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun m => Spec.map (CommRingCat.ofHom m)) (congrArg AlgHom.toRingHom h)

variable {E}

def Data.lineTrace (A : B.Obj .line) (z : E) : ℂ :=
  R.trace E (X := .line) (linePoint z) A

/-- The former torus arithmetic fibers and operators are specializations
of the same rational-point system, with finite dimensionality retained. -/
abbrev Data.torusArithmetic : TorusArithmeticData p (B.Obj .torus) where
  fiber L _ _ _ x y := R.fiber L .torus (PhysicalTorusMorphism.schemePoint x y)
  frobenius L _ _ _ x y := R.frobenius L .torus (PhysicalTorusMorphism.schemePoint x y)
  finite L _ _ _ x y A := R.finite L .torus (PhysicalTorusMorphism.schemePoint x y) A

variable {Point : Type h} (D : CurveData (B.Obj .source) Point)

def Data.curveTraceData (point : Point) (lambda xi : Eˣ) : CurveTraceData D E where
  point := point
  trace A x := R.trace E (X := .source) (curvePoint x lambda xi) A

/-- The geometric point choice is separate; its trace is always the
same arithmetic source stalk, for every finite extension. -/
abbrev Data.curveTraceFamily
    (point : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], Lˣ → Lˣ → Point) :
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], Lˣ → Lˣ → CurveTraceData D L :=
  fun L _ _ _ x y => R.curveTraceData (E := L) D (point L x y) x y

/-- The coordinate trace interface is derived at the actual source point. -/
theorem Data.curvePullback (point : Point) (lambda xi : Eˣ) :
    PullbackTraceRules (originalPullbackData (ZMod p) B.geometricPullbacks)
      (R.curveTraceData D point lambda xi) R.lineTrace lambda xi where
  pullback g A x := by
    change R.trace E (X := .source) (curvePoint x lambda xi) ((B.pull (X := .source) (Y := .line) (Spec.map (CommRingCat.ofHom g.toRingHom))).obj A) = _
    rw [R.pullback_trace E (X := .source) (Y := .line), curvePoint_comp]
    rfl

/-- Torus pullback also uses the same Frobenius operators and genuine points. -/
theorem Data.torusPullback (f : PhysicalTorusMorphism.torusScheme (ZMod p) ⟶
      PhysicalTorusMorphism.torusScheme (ZMod p)) (A : B.Obj .torus) (x y x' y' : Eˣ)
    (h : PhysicalTorusMorphism.schemePoint (K := ZMod p) x y ≫ f =
      PhysicalTorusMorphism.schemePoint (K := ZMod p) x' y') :
    R.torusArithmetic.trace E ((B.pull (X := .torus) (Y := .torus) f).obj A) x y =
      R.torusArithmetic.trace E A x' y' := by
  change R.trace E (X := .torus) _ ((B.pull (X := .torus) (Y := .torus) f).obj A) = R.trace E (X := .torus) _ A
  rw [R.pullback_trace E (X := .torus) (Y := .torus), h]

/-- Primitive operations before any independent choice of trace function. -/
structure PrimitiveOperations (p : ℕ) [Fact p.Prime] (Line : Type) where
  artinSchreier : AddChar (ZMod p) (PadicAlgCl 2) → Line
  kloosterman3 : AddChar (ZMod p) (PadicAlgCl 2) → Line
  twistOne : Line → Line

/-- The primitive source trace is the same rational-point Frobenius trace. -/
abbrev PrimitiveOperations.primitive (O : PrimitiveOperations p (B.Obj .line)) :
    PublishedPrimitiveSources.Data p (B.Obj .line) where
  artinSchreier := O.artinSchreier
  kloosterman3 := O.kloosterman3
  twistOne := O.twistOne
  trace L _ _ _ := R.lineTrace (E := L)

/-- Retained general torus geometry, tensor and dual/Tate laws. The
pullback trace clause is supplied by the shared rational-point stalks. -/
structure TorusOtherRules (P : ParameterData (B.Obj .torus)) : Prop where
  pullback_lisse : ∀ f A, P.Lisse A → P.Lisse ((B.torusOperations.pullback f).obj A)
  pullback_pure : ∀ f A a, P.Pure A a → P.Pure ((B.torusOperations.pullback f).obj A) a
  unit_lisse : P.Lisse (𝟙_ (B.Obj .torus))
  unit_pure : P.Pure (𝟙_ (B.Obj .torus)) 0
  tensor_lisse : ∀ A B, P.Lisse A → P.Lisse B → P.Lisse (A ⊗ B)
  tensor_pure : ∀ A B a b, P.Pure A a → P.Pure B b → P.Pure (A ⊗ B) (a + b)
  unit_trace : ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L],
    ∀ x y : Lˣ, R.torusArithmetic.trace L (𝟙_ (B.Obj .torus)) x y = 1
  tensor_trace : ∀ A B, P.Lisse A → P.Lisse B →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : Lˣ,
      R.torusArithmetic.trace L (A ⊗ B) x y = R.torusArithmetic.trace L A x y * R.torusArithmetic.trace L B x y
  dualTate_trace : ∀ A, P.Lisse A → P.Pure A 1 →
    ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod p) L], ∀ x y : Lˣ,
      R.torusArithmetic.trace L (P.dualTateMinusOne A) x y = star (R.torusArithmetic.trace L A x y)

variable {P : ParameterData (B.Obj .torus)}

/-- The old torus interface uses the derived actual-point pullback trace. -/
theorem TorusOtherRules.rules (T : TorusOtherRules R P) :
    TorusRules P B.torusOperations R.torusArithmetic where
  pullback_lisse := T.pullback_lisse
  pullback_pure := T.pullback_pure
  unit_lisse := T.unit_lisse
  unit_pure := T.unit_pure
  tensor_lisse := T.tensor_lisse
  tensor_pure := T.tensor_pure
  unit_trace := T.unit_trace
  tensor_trace := T.tensor_trace
  dualTate_trace := T.dualTate_trace
  pullback_trace f A _ L _ _ _ x y x' y' h := R.torusPullback (E := L) f A x y x' y' h

end PrimeGap182.TypeIII.RationalPointStalks

#print axioms PrimeGap182.TypeIII.RationalPointStalks.Data.pullback_trace
#print axioms PrimeGap182.TypeIII.RationalPointStalks.curvePoint_comp
#print axioms PrimeGap182.TypeIII.RationalPointStalks.Data.torusArithmetic
#print axioms PrimeGap182.TypeIII.RationalPointStalks.Data.curveTraceData
#print axioms PrimeGap182.TypeIII.RationalPointStalks.Data.curvePullback
#print axioms PrimeGap182.TypeIII.RationalPointStalks.Data.torusPullback
#print axioms PrimeGap182.TypeIII.RationalPointStalks.PrimitiveOperations.primitive

#print axioms PrimeGap182.TypeIII.RationalPointStalks.TorusOtherRules.rules
