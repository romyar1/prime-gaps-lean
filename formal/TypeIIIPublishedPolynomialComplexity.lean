import TypeIIIPhysicalTorusLaurent

/-!
# Applying QST to the actual physical morphism

QST Proposition 6.21 is supplied as a rule for every polynomial
endomorphism of the fixed closed torus in A4, not as a bound for the
correlation family. The source is a reduced integral closed subscheme:
`TypeIIIPhysicalTorusLaurent` proves the Laurent algebra equivalence,
the prime defining ideal and the closed immersion.

The physical-map estimate below substitutes the actual coordinate ring
endomorphism and its proved polynomial presentation. Its degree bound is
six and its two defining equations are quadratic. Over a non-algebraically
closed field, complexity is defined after geometric base change, as in
QST Remark 6.9. The bound is unchanged over finite extensions.

Source: Sawin--Forey--Fresan--Kowalski, Quantitative sheaf theory,
https://arxiv.org/pdf/2101.00635v4, Proposition 6.21 (printed p.38).
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.PublishedPolynomialComplexity

open PhysicalTorusMorphism PhysicalPolynomialMap

universe u

variable {K : Type u} [Field K]

/-- The numerical morphism complexity at the fixed torus embeddings. -/
abbrev TorusMorphismComplexity (K : Type u) [Field K] :=
  (torusScheme K ⟶ torusScheme K) → ℕ

/-- The published polynomial-morphism theorem at the actual closed
torus. It quantifies over all ring maps and polynomial presentations;
it contains no physical parameters, core sheaves, or Fourier bounds. -/
structure TorusPolynomialRules (c : TorusMorphismComplexity K) : Prop where
  bound : ∀ (g : TorusRing K →ₐ[K] TorusRing K)
    (G : Fin 4 → MvPolynomial (Fin 4) K) (d : ℕ),
    2 ≤ d →
    g.comp (quotient K) = MvPolynomial.aeval (fun i => quotient K (G i)) →
    (∀ i, (G i).totalDegree ≤ d) →
    c (Spec.map (CommRingCat.ofHom g.toRingHom)) ≤ polynomialMapBound 4 4 2 d

variable {c : TorusMorphismComplexity K} (R : TorusPolynomialRules c)

include R in
/-- The generic QST bound applied to the original physical map. -/
theorem physical_complexity_le (α m n : Kˣ) :
    c (physicalMorphism K α m n) ≤ polynomialMapBound 4 4 2 6 :=
  R.bound (physicalEnd K α m n) (physicalPolynomials (α : K) (m : K) (n : K)) 6
    (by norm_num) (physicalEnd_polynomial_presentation K α m n)
    (physicalPolynomials_degree_le (α : K) (m : K) (n : K))

include R in
theorem physical_complexity_le_explicit (α m n : Kˣ) :
    c (physicalMorphism K α m n) ≤ 34646092416 := by
  simpa only [physical_polynomialMapBound] using physical_complexity_le R α m n

end PrimeGap182.TypeIII.PublishedPolynomialComplexity

#print axioms PrimeGap182.TypeIII.PublishedPolynomialComplexity.TorusMorphismComplexity
#print axioms PrimeGap182.TypeIII.PublishedPolynomialComplexity.TorusPolynomialRules
#print axioms PrimeGap182.TypeIII.PublishedPolynomialComplexity.TorusPolynomialRules.mk
#print axioms PrimeGap182.TypeIII.PublishedPolynomialComplexity.TorusPolynomialRules.bound
#print axioms PrimeGap182.TypeIII.PublishedPolynomialComplexity.physical_complexity_le
#print axioms PrimeGap182.TypeIII.PublishedPolynomialComplexity.physical_complexity_le_explicit
