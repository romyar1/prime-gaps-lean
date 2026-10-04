import TypeIIIArithmeticPrimitivesFromCommonKatzConstruction
import TypeIIIRationalPointStalksFromUniversalFiber
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Primitive traces from general coefficient Frobenius formulas

ONE ordinary finite-field coefficient fiber over Qbar2 is compared to the
existing complex arithmetic fiber by actual extension of scalars. General
ALL-object Frobenius compatibility and Mathlib trace_baseChange derive trace
transport. The raw Katz formula quantifies over ALL finite base fields,
ALL positive Kloosterman ranks and ALL finite-extension unit points. The
Artin--Schreier rank-one Frobenius description quantifies over ALL finite
base fields and ALL affine-line points. Characters are extended by the
actual algebraic field trace, and the fixed complex embedding maps the
finite sums. No selected prime trace clause or whole primitive Rules is
assumed.

ALL-ordinary zero-extension restriction to the actual native Gm chart is
explicit general operator interpretation. SAME-U composition and the proved
coordinate point factorization derive restriction at every unit point.
The interpretation of C/O, coefficient fibers and Frobenius as continuous
finite-coefficient etale/adic models remains external. The primary formulas
are Katz GKM 4.1.1(2) (printed49) and 4.3(1) (printed59).
https://web.math.princeton.edu/~nmk/Katz-GKM.pdf
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators Classical TensorProduct

namespace PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas
open ExactInverseImagesToDerived QSTPrimitiveBridgesFromCommonKatzConstruction
open RationalPointStalksFromUniversalFiber TwoAdicComplexEmbedding

abbrev Coefficient := PadicAlgCl 2

/-- Actual finite-extension additive character; no independent dictionary. -/
def extension {K : Type} [Field K] (ψ : AddChar K Coefficient)
    (E : Type) [Field E] [Algebra K E] : AddChar E Coefficient :=
  ψ.compAddMonoidHom (Algebra.trace K E).toAddMonoidHom

/-- The product-constrained raw sum, for EVERY rank including rank one. -/
def rawSum {E : Type} [Field E] [Fintype E] (ψ : AddChar E Coefficient)
    (n : ℕ) (z : Eˣ) : Coefficient :=
  ∑ v : Fin n → Eˣ, if (∏ i, v i) = z then ψ (∑ i, (v i : E)) else 0

/-- The genuine Laurent point has its actual coefficient evaluation. -/
def gmEvaluation (K E : Type) [Field K] [Field E] [Algebra K E] (z : Eˣ) :
    LaurentPolynomial K →ₐ[K] E where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap K E) z
  commutes' c := LaurentPolynomial.eval₂_C _ _ c

def gmPoint (K E : Type) [Field K] [Field E] [Algebra K E] (z : Eˣ) :
    Spec (.of E) ⟶ ArithmeticSourceMaps.fiberScheme K :=
  Spec.map (CommRingCat.ofHom (gmEvaluation K E z).toRingHom)

/-- Every unit line point factors through the SAME actual native open chart. -/
theorem gmPoint_comp (K E : Type) [Field K] [Field E] [Algebra K E] (z : Eˣ) :
    gmPoint K E z ≫ ArithmeticSourceMaps.localInputMorphism K K =
      RationalPointStalks.linePoint (K := K) (z : E) := by
  have h : (gmEvaluation K E z).comp (ArithmeticSourceMaps.localInputHom K K) =
      MvPolynomial.aeval (R := K) (fun _ : Fin 1 => (z : E)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, ArithmeticSourceMaps.localInputHom, MvPolynomial.aeval_X]
    change LaurentPolynomial.eval₂ (algebraMap K E) z (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
  dsimp only [gmPoint, ArithmeticSourceMaps.localInputMorphism, RationalPointStalks.linePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (congrArg AlgHom.toRingHom h)

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (F : ArithmeticFibers C) (O : Constructions C)

/-- General coefficient fibers, on ALL ordinary objects of ALL finite fields.
The comparison is the actual scalar-extension functor, not a trace law.
Continuous finite-coefficient/adic interpretation is not constructed here. -/
structure CoefficientFibers where
  fiber : ∀ (E : Type) [Field E] [Fintype E], C (Spec (.of E)) ⥤ ModuleCat.{0} Coefficient
  frobenius : ∀ (E : Type) [Field E] [Fintype E], fiber E ⟶ fiber E
  finite : ∀ (E : Type) [Field E] [Fintype E] A,
    FiniteDimensional Coefficient ((fiber E).obj A)
  complexComparison : ∀ (E : Type) [Field E] [Fintype E],
    F.fiber E ≅ fiber E ⋙ ModuleCat.extendScalars complexEquiv.toRingHom
  complexFrobenius : ∀ (E : Type) [Field E] [Fintype E] (A : C (Spec (.of E))),
    ((complexComparison E).app A).toLinearEquiv.conj ((F.frobenius E).app A).hom =
      ((ModuleCat.extendScalars complexEquiv.toRingHom).map ((frobenius E).app A)).hom

variable (B : CoefficientFibers C F)

def coefficientTrace (E : Type) [Field E] [Fintype E] (A : C (Spec (.of E))) : Coefficient :=
  LinearMap.trace Coefficient ((B.fiber E).obj A) ((B.frobenius E).app A).hom

def complexTrace (E : Type) [Field E] [Fintype E] (A : C (Spec (.of E))) : ℂ :=
  LinearMap.trace ℂ ((F.fiber E).obj A) ((F.frobenius E).app A).hom

omit [∀ X, Abelian (C X)] in
/-- Scalar-extension trace is computed by existing finite-free linear algebra. -/
theorem complexTrace_eq (E : Type) [Field E] [Fintype E] (A : C (Spec (.of E))) :
    complexTrace C F E A = complexEquiv (coefficientTrace C F B E A) := by
  have := B.finite E A
  let e := ((B.complexComparison E).app A).toLinearEquiv
  have h := (LinearMap.trace_conj' ((F.frobenius E).app A).hom e).symm
  have ht := congrArg (LinearMap.trace ℂ ((B.fiber E ⋙ ModuleCat.extendScalars complexEquiv.toRingHom).obj A))
    (B.complexFrobenius E A)
  have hb : LinearMap.trace ℂ
      ((ModuleCat.extendScalars complexEquiv.toRingHom).obj ((B.fiber E).obj A))
      ((ModuleCat.extendScalars complexEquiv.toRingHom).map ((B.frobenius E).app A)).hom =
      complexEquiv (coefficientTrace C F B E A) := by
    let _ : Algebra Coefficient ℂ := complexEquiv.toRingHom.toAlgebra
    change LinearMap.trace ℂ (ℂ ⊗[Coefficient] ((B.fiber E).obj A))
      (((B.frobenius E).app A).hom.baseChange ℂ) = _
    exact LinearMap.trace_baseChange _ ℂ
  exact h.trans (ht.trans hb)

omit [∀ X, Abelian (C X)] in
/-- Naturality of ONE Frobenius computes conjugacy for ANY ordinary iso. -/
theorem complexTrace_iso (E : Type) [Field E] [Fintype E]
    {A D : C (Spec (.of E))} (e : A ≅ D) :
    complexTrace C F E A = complexTrace C F E D := by
  let l := (F.fiber E).mapIso e
  have hn (v) : l.toLinearEquiv (((F.frobenius E).app A).hom v) =
      ((F.frobenius E).app D).hom (l.toLinearEquiv v) :=
    congrArg (fun m => m.hom v) ((F.frobenius E).naturality e.hom).symm
  have hc : l.toLinearEquiv.conj ((F.frobenius E).app A).hom =
      ((F.frobenius E).app D).hom := by
    ext v
    simpa using hn (l.toLinearEquiv.symm v)
  exact (LinearMap.trace_conj' ((F.frobenius E).app A).hom l.toLinearEquiv).symm.trans
    (congrArg (LinearMap.trace ℂ ((F.fiber E).obj D)) hc)

variable (zeroRestriction : ∀ (K : Type) [Field K] (h2 : (2 : K) ≠ 0),
  O.zero K h2 ⋙ U.pull (ArithmeticSourceMaps.localInputMorphism K K) ≅ 𝟭 _)

/-- ALL ordinary objects, ALL extension unit points, on the SAME zero operator. -/
def zeroPointIso (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (E : Type) [Field E] [Algebra K E] (z : Eˣ) :
    O.zero K h2 ⋙ U.pull (RationalPointStalks.linePoint (K := K) (z : E)) ≅
      U.pull (gmPoint K E z) := by
  rw [← gmPoint_comp K E z]
  exact Functor.isoWhiskerLeft (O.zero K h2)
      (U.composition (gmPoint K E z) (ArithmeticSourceMaps.localInputMorphism K K)).symm ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (zeroRestriction K h2) (U.pull (gmPoint K E z)) ≪≫
    Functor.leftUnitor _

/-- Precise general family formulas, independent of the prime.
The rank-one AS fields describe actual stalk/Frobenius operators rather than
assuming their trace. Katz's formula covers every positive raw rank and has
no zero-extension or Tate-twisted object in its theorem domain. -/
structure PublishedCoefficientFormulas where
  kloosterman : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (z : Eˣ),
    coefficientTrace C F B E ((U.pull (gmPoint K E z)).obj
      (O.katz K h2 (kloostermanIndex ψ hψ n hn 0))) =
        (-1 : Coefficient)^(n - 1) * rawSum (extension ψ E) n z
  asBasis : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (_hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (z : E),
    (B.fiber E).obj ((U.pull (RationalPointStalks.linePoint (K := K) z)).obj
      (O.artinSchreier K h2 ψ)) ≅ ModuleCat.of Coefficient Coefficient
  asFrobenius : ∀ (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (z : E),
    (asBasis K h2 ψ hψ E z).toLinearEquiv.conj
      ((B.frobenius E).app ((U.pull (RationalPointStalks.linePoint (K := K) z)).obj
        (O.artinSchreier K h2 ψ))).hom = extension ψ E z • LinearMap.id

variable (T : PublishedCoefficientFormulas C U F O B)

include T in
/-- The AS trace is a conclusion of its general rank-one Frobenius description. -/
theorem coefficient_as_trace (K : Type) [Field K] [Fintype K] (h2 : (2 : K) ≠ 0)
    (ψ : AddChar K Coefficient) (hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra K E] (z : E) :
    coefficientTrace C F B E ((U.pull (RationalPointStalks.linePoint (K := K) z)).obj
      (O.artinSchreier K h2 ψ)) = extension ψ E z := by
  let e := (T.asBasis K h2 ψ hψ E z).toLinearEquiv
  have h := (LinearMap.trace_conj'
    ((B.frobenius E).app ((U.pull (RationalPointStalks.linePoint (K := K) z)).obj
      (O.artinSchreier K h2 ψ))).hom e).symm
  have ht := congrArg (LinearMap.trace Coefficient Coefficient) (T.asFrobenius K h2 ψ hψ E z)
  exact h.trans (ht.trans (by simp only [map_smul, LinearMap.trace_id, CommSemiring.finrank_self,
    Nat.cast_one, smul_eq_mul, mul_one]))

private def tripleEquiv (E : Type) [Field E] : (Fin 3 → Eˣ) ≃ Eˣ × (Eˣ × Eˣ) where
  toFun v := (v 0, v 1, v 2)
  invFun v := ![v.1, v.2.1, v.2.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv v := by rcases v with ⟨a, b, c⟩; rfl

/-- Checked finite-sum embedding and rank-three tuple reindexing. -/
theorem rawSum_three_complex {E : Type} [Field E] [Fintype E]
    (ψ : AddChar E Coefficient) (z : Eˣ) :
    complexEquiv (rawSum ψ 3 z) =
      KatzSourceNormalization.rawKl3 (complexEquiv.toMonoidHom.compAddChar ψ) z := by
  have hraw : rawSum ψ 3 z =
      ∑ a : Eˣ, ∑ b : Eˣ, ∑ c : Eˣ,
        if a * b * c = z then ψ ((a : E) + (b : E) + (c : E)) else 0 := by
    unfold rawSum
    have h := Fintype.sum_equiv (tripleEquiv E)
      (fun v : Fin 3 → Eˣ => if (∏ i, v i) = z then ψ (∑ i, (v i : E)) else 0)
      (fun v : Eˣ × (Eˣ × Eˣ) => if v.1 * v.2.1 * v.2.2 = z then
        ψ ((v.1 : E) + (v.2.1 : E) + (v.2.2 : E)) else 0)
      (by intro v; simp [tripleEquiv, Fin.prod_univ_three, Fin.sum_univ_three, mul_assoc, add_assoc])
    simpa only [Fintype.sum_prod_type] using h
  rw [hraw]
  simp only [map_sum, KatzSourceNormalization.rawKl3]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rfl
  · exact map_zero _

variable [∀ X, MonoidalCategory (C X)]
  [∀ {X Y : Scheme} (f : X ⟶ Y), (U.pull f).Monoidal]

include zeroRestriction T in
/-- The exact old rawTrace field, derived for ALL nontrivial prime characters. -/
theorem primitive_raw_trace (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (z : Eˣ) :
    let D := RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
      (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)
    D.trace E (D.kloosterman3 ψ) (z : E) =
      (-1 : ℂ)^(3 - 1) * KatzSourceNormalization.rawKl3
        (PublishedPrimitiveSources.complexCharacter p ψ E) z := by
  dsimp only
  rw [ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations_kloosterman3_nontrivial
    C O p h2 ψ hψ]
  change complexTrace C F E ((U.pull (RationalPointStalks.linePoint (z : E))).obj
    ((O.zero (ZMod p) h2).obj (O.katz (ZMod p) h2 (kloostermanIndex ψ hψ 3 (by decide) 0)))) = _
  have hzero := complexTrace_iso C F E
    ((zeroPointIso C U O zeroRestriction (ZMod p) h2 E z).app
      (O.katz (ZMod p) h2 (kloostermanIndex ψ hψ 3 (by decide) 0)))
  change complexTrace C F E ((U.pull (RationalPointStalks.linePoint (z : E))).obj
      ((O.zero (ZMod p) h2).obj (O.katz (ZMod p) h2 (kloostermanIndex ψ hψ 3 (by decide) 0)))) =
    complexTrace C F E ((U.pull (gmPoint (ZMod p) E z)).obj
      (O.katz (ZMod p) h2 (kloostermanIndex ψ hψ 3 (by decide) 0))) at hzero
  rw [hzero, complexTrace_eq C F B E, T.kloosterman (ZMod p) h2 ψ hψ 3 (by decide) E z,
    map_mul, map_pow, map_neg, map_one, rawSum_three_complex]
  rfl

include T in
/-- The exact old asTrace field, derived at ALL line points including zero. -/
theorem primitive_as_trace (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (ψ : AddChar (ZMod p) Coefficient) (hψ : ψ ≠ 1)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] (z : E) :
    let D := RationalPointStalks.PrimitiveOperations.primitive (pointStalks C U F p)
      (ArithmeticPrimitivesFromCommonKatzConstruction.primitiveOperations C O p h2)
    D.trace E (D.artinSchreier ψ) z =
      complexEquiv (PublishedPrimitiveSources.extension p ψ E z) := by
  change complexTrace C F E ((U.pull (RationalPointStalks.linePoint z)).obj
    (O.artinSchreier (ZMod p) h2 ψ)) = _
  rw [complexTrace_eq C F B E, coefficient_as_trace C U F O B T (ZMod p) h2 ψ hψ E z]
  rfl

end PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas

-- Declaration reports consumed by the repository-wide axiom audit.
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.Coefficient
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.extension
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.rawSum
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.gmEvaluation
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.gmPoint
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.gmPoint_comp
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.CoefficientFibers
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.coefficientTrace
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.complexTrace
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.complexTrace_eq
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.complexTrace_iso
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.zeroPointIso
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.PublishedCoefficientFormulas
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.coefficient_as_trace
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.rawSum_three_complex
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.primitive_raw_trace
#print axioms PrimeGap182.TypeIII.PrimitiveTracesFromGeneralKatzArtinSchreierFormulas.primitive_as_trace
