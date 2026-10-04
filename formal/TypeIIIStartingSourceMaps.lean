import TypeIIIPublishedConstructionComplexity

/-!
# The three starting maps on the actual parameterized curve

The source is the closed affine presentation of Gm^3 with coordinates
(x, xInv, lambda, lambdaInv, xi, xiInv). Its three maps to A1 are x,
lambda*x and xi*x. All equations and map coordinates have degree at most
two. The source ring embeds in a Laurent polynomial ring over the already
proved two-dimensional torus ring, so the presentation is integral.

QST Proposition 6.21 is an explicit general rule for polynomial maps from
this fixed source. It yields one bound for the three genuine Spec maps.
No sheaf or Type III estimate is asserted in this module.
Source: https://arxiv.org/html/2101.00635v4, Proposition 6.21.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.StartingSourceMaps

universe u
variable (K : Type u) [Field K]

def equations : Fin 3 → MvPolynomial (Fin 6) K :=
  ![X 0 * X 1 - 1, X 2 * X 3 - 1, X 4 * X 5 - 1]

def sourceIdeal : Ideal (MvPolynomial (Fin 6) K) :=
  Ideal.span (Set.range (equations K))

abbrev SourceRing := MvPolynomial (Fin 6) K ⧸ sourceIdeal K

def quotient : MvPolynomial (Fin 6) K →ₐ[K] SourceRing K :=
  Ideal.Quotient.mkₐ K (sourceIdeal K)

def coordinate (i : Fin 6) : SourceRing K := quotient K (X i)

theorem quotient_equation (i : Fin 3) : quotient K (equations K i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

def coordinateUnit (i : Fin 3) : (SourceRing K)ˣ where
  val := ![coordinate K 0, coordinate K 2, coordinate K 4] i
  inv := ![coordinate K 1, coordinate K 3, coordinate K 5] i
  val_inv := by
    have h := quotient_equation K i
    fin_cases i <;> simpa [equations, coordinate, sub_eq_zero] using h
  inv_val := by
    rw [mul_comm]
    have h := quotient_equation K i
    fin_cases i <;> simpa [equations, coordinate, sub_eq_zero] using h

variable {K} {A : Type u} [CommRing A] [Algebra K A]

def unitCoordinates (x l t : Aˣ) : Fin 6 → A :=
  ![(x : A), (↑x⁻¹ : A), (l : A), (↑l⁻¹ : A), (t : A), (↑t⁻¹ : A)]

/-- Universal evaluation over any coefficient algebra, not only fields. -/
def evaluation (x l t : Aˣ) : SourceRing K →ₐ[K] A := by
  let f : MvPolynomial (Fin 6) K →ₐ[K] A := aeval (unitCoordinates x l t)
  apply Ideal.Quotient.liftₐ (sourceIdeal K) f
  have hker : sourceIdeal K ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f (equations K i) = 0
    fin_cases i <;> simp [f, equations, unitCoordinates]
  exact fun a ha => hker ha

theorem evaluation_coordinate (x l t : Aˣ) (i : Fin 6) :
    evaluation (K := K) x l t (coordinate K i) = unitCoordinates x l t i := by
  change aeval (unitCoordinates x l t) (X i) = _
  exact aeval_X _ _

variable (K)

abbrev LaurentModel := LaurentPolynomial (PhysicalTorusMorphism.TorusRing K)

def laurentUnits : Fin 3 → (LaurentModel K)ˣ :=
  ![Units.map (LaurentPolynomial.C : PhysicalTorusMorphism.TorusRing K →+*
      LaurentModel K) (PhysicalTorusMorphism.xUnit K),
    Units.map (LaurentPolynomial.C : PhysicalTorusMorphism.TorusRing K →+*
      LaurentModel K) (PhysicalTorusMorphism.yUnit K),
    PhysicalTorusLaurent.variableUnit (PhysicalTorusMorphism.TorusRing K)]

def toLaurent : SourceRing K →ₐ[K] LaurentModel K :=
  evaluation (K := K) (A := LaurentModel K)
    (laurentUnits K 0) (laurentUnits K 1) (laurentUnits K 2)

def fromLaurent : LaurentModel K →ₐ[K] SourceRing K where
  toRingHom := LaurentPolynomial.eval₂
    (PhysicalTorusMorphism.evaluation (coordinateUnit K 0) (coordinateUnit K 1)).toRingHom
    (coordinateUnit K 2)
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _
      (LaurentPolynomial.C (algebraMap K (PhysicalTorusMorphism.TorusRing K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact AlgHom.commutes _ c

/-- The original quotient embeds in the domain Laurent model. -/
theorem fromLaurent_comp_toLaurent :
    (fromLaurent K).comp (toLaurent K) = AlgHom.id K (SourceRing K) := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change fromLaurent K (evaluation _ _ _ (coordinate K i)) = coordinate K i
  rw [evaluation_coordinate]
  fin_cases i <;>
    simp [unitCoordinates, laurentUnits, fromLaurent, PhysicalTorusLaurent.variableUnit,
      PhysicalTorusMorphism.xUnit, PhysicalTorusMorphism.yUnit,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      PhysicalTorusMorphism.evaluation_coordinate, coordinateUnit]

theorem toLaurent_injective : Function.Injective (toLaurent K) := by
  intro a b h
  have ha := DFunLike.congr_fun (fromLaurent_comp_toLaurent K) a
  have hb := DFunLike.congr_fun (fromLaurent_comp_toLaurent K) b
  exact ha.symm.trans ((congrArg (fromLaurent K) h).trans hb)

instance sourceRing_isDomain : IsDomain (SourceRing K) :=
  Function.Injective.isDomain (toLaurent K) (toLaurent_injective K)

theorem sourceIdeal_isPrime : (sourceIdeal K).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime (sourceIdeal K)).mp inferInstance

abbrev sourceScheme : Scheme := Spec (.of (SourceRing K))
abbrev affineLine : Scheme := Spec (.of (MvPolynomial (Fin 1) K))

instance sourceScheme_isIntegral : AlgebraicGeometry.IsIntegral (sourceScheme K) := by
  change AlgebraicGeometry.IsIntegral (Spec (.of (SourceRing K)))
  infer_instance

def sourceEmbedding : sourceScheme K ⟶ Spec (.of (MvPolynomial (Fin 6) K)) :=
  Spec.map (CommRingCat.ofHom (quotient K).toRingHom)

instance sourceEmbedding_isClosedImmersion : IsClosedImmersion (sourceEmbedding K) := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sourceIdeal K))))
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

def polynomials : Fin 3 → MvPolynomial (Fin 6) K :=
  ![X 0, X 2 * X 0, X 4 * X 0]

def inputHom (i : Fin 3) : MvPolynomial (Fin 1) K →ₐ[K] SourceRing K :=
  aeval (fun _ => quotient K (polynomials K i))

def inputMorphism (i : Fin 3) : sourceScheme K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (inputHom K i).toRingHom)

/-- Exact pullback of the affine-line coordinate, over every algebra. -/
theorem inputHom_evaluation (x l t : Aˣ) (i : Fin 3) :
    evaluation (K := K) x l t (inputHom K i (X 0)) =
      ![(x : A), (l : A) * x, (t : A) * x] i := by
  simp only [inputHom, aeval_X]
  change aeval (unitCoordinates x l t) (polynomials K i) = _
  fin_cases i <;> simp [polynomials, unitCoordinates]

theorem equations_degree_le (i : Fin 3) : (equations K i).totalDegree ≤ 2 := by
  have h (a b : Fin 6) : (X a * X b - 1 : MvPolynomial (Fin 6) K).totalDegree ≤ 2 :=
    (totalDegree_sub_C_le _ 1).trans ((totalDegree_mul _ _).trans (by simp))
  fin_cases i
  · exact h 0 1
  · exact h 2 3
  · exact h 4 5

theorem polynomials_degree_le (i : Fin 3) : (polynomials K i).totalDegree ≤ 2 := by
  have h (a b : Fin 6) : (X a * X b : MvPolynomial (Fin 6) K).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simp)
  fin_cases i
  · simp [polynomials]
  · exact h 2 0
  · exact h 4 0

abbrev MorphismComplexity := (sourceScheme K ⟶ affineLine K) → ℕ

/-- QST 6.21 at the fixed A6 and A1 embeddings, with all three source
equations included. Complexity is taken after geometric base change. -/
structure PolynomialRules (c : MorphismComplexity K) : Prop where
  bound : ∀ (g : MvPolynomial (Fin 1) K →ₐ[K] SourceRing K)
    (F : Fin 1 → MvPolynomial (Fin 6) K) (d : ℕ),
    (∀ i, (equations K i).totalDegree ≤ d) →
    g = aeval (fun i => quotient K (F i)) →
    (∀ i, (F i).totalDegree ≤ d) →
    c (Spec.map (CommRingCat.ofHom g.toRingHom)) ≤
      PhysicalPolynomialMap.polynomialMapBound 6 1 3 d

theorem input_morphism_complexity_le {c : MorphismComplexity K}
    (Q : PolynomialRules K c) (i : Fin 3) :
    c (inputMorphism K i) ≤ 1870768416 := by
  have h := Q.bound (inputHom K i) (fun _ => polynomials K i) 2
    (equations_degree_le K) rfl (fun _ => polynomials_degree_le K i)
  norm_num [PhysicalPolynomialMap.polynomialMapBound] at h ⊢
  exact h

end PrimeGap182.TypeIII.StartingSourceMaps

#print axioms PrimeGap182.TypeIII.StartingSourceMaps.quotient_equation
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.evaluation_coordinate
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.fromLaurent_comp_toLaurent
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.toLaurent_injective
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.sourceRing_isDomain
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.sourceIdeal_isPrime
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.sourceScheme_isIntegral
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.sourceEmbedding_isClosedImmersion
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.inputHom_evaluation
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.equations_degree_le
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.polynomials_degree_le
#print axioms PrimeGap182.TypeIII.StartingSourceMaps.input_morphism_complexity_le
