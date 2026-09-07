import TypeIIIArtinSchreierCover

/-!
# Base change of the actual Artin--Schreier quotient

The tensor product of the quotient algebra with a coefficient extension
is identified with the quotient by the same polynomial over that extension.
Both maps are given by the universal properties of the tensor product and
the polynomial quotient. In particular, this does not require the quotient
or the coefficient extension to be a domain.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open Polynomial
open scoped TensorProduct

variable (p : ℕ) {R : Type*} [CommRing R]
  (S : Type*) [CommRing S] [Algebra R S] (f : R)

/-- The defining polynomial commutes with coefficient extension. -/
theorem artinSchreierPolynomial_map :
    (artinSchreierPolynomial p f).map (algebraMap R S) =
      artinSchreierPolynomial p (algebraMap R S f) := by
  simp only [artinSchreierPolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]

/-- The quotient map after extending the coefficients sends root to root. -/
def artinSchreierCover_baseMap :
    ArtinSchreierCover p R f →ₐ[R]
      ArtinSchreierCover p S (algebraMap R S f) :=
  AdjoinRoot.liftAlgHom (artinSchreierPolynomial p f)
    (Algebra.ofId R (ArtinSchreierCover p S (algebraMap R S f)))
    (artinSchreierRoot p (algebraMap R S f)) (by
      simp only [artinSchreierPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      change artinSchreierRoot p (algebraMap R S f) ^ p -
          artinSchreierRoot p (algebraMap R S f) -
          algebraMap R (ArtinSchreierCover p S (algebraMap R S f)) f = 0
      rw [artinSchreierRoot_relation,
        IsScalarTower.algebraMap_apply R S (ArtinSchreierCover p S (algebraMap R S f)),
        sub_self])

@[simp] theorem artinSchreierCover_baseMap_root :
    artinSchreierCover_baseMap p S f (artinSchreierRoot p f) =
      artinSchreierRoot p (algebraMap R S f) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The root in the tensor product satisfies the coefficient-extended equation. -/
theorem artinSchreier_tensorRoot_relation :
    (1 ⊗ₜ[R] artinSchreierRoot p f : S ⊗[R] ArtinSchreierCover p R f) ^ p -
        (1 ⊗ₜ[R] artinSchreierRoot p f) =
      algebraMap S (S ⊗[R] ArtinSchreierCover p R f) (algebraMap R S f) := by
  have h := congrArg
    (Algebra.TensorProduct.includeRight :
      ArtinSchreierCover p R f →ₐ[R] S ⊗[R] ArtinSchreierCover p R f)
    (artinSchreierRoot_relation p f)
  simpa only [map_sub, map_pow, AlgHom.commutes,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, one_pow,
    IsScalarTower.algebraMap_apply R S (S ⊗[R] ArtinSchreierCover p R f)] using h

/-- The forward map of the actual quotient base-change isomorphism. -/
def artinSchreierCover_baseChangeHom :
    S ⊗[R] ArtinSchreierCover p R f →ₐ[S]
      ArtinSchreierCover p S (algebraMap R S f) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId S (ArtinSchreierCover p S (algebraMap R S f)))
    (artinSchreierCover_baseMap p S f) (fun _ _ => Commute.all _ _)

/-- The inverse map sends the adjoined root to the literal tensor root. -/
def artinSchreierCover_baseChangeInv :
    ArtinSchreierCover p S (algebraMap R S f) →ₐ[S]
      S ⊗[R] ArtinSchreierCover p R f :=
  AdjoinRoot.liftAlgHom (artinSchreierPolynomial p (algebraMap R S f))
    (Algebra.ofId S (S ⊗[R] ArtinSchreierCover p R f))
    (1 ⊗ₜ[R] artinSchreierRoot p f) (by
      simp only [artinSchreierPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact sub_eq_zero.mpr (artinSchreier_tensorRoot_relation p S f))

@[simp] theorem artinSchreierCover_baseChangeInv_root :
    artinSchreierCover_baseChangeInv p S f
        (artinSchreierRoot p (algebraMap R S f)) =
      1 ⊗ₜ[R] artinSchreierRoot p f :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] theorem artinSchreierCover_baseChangeHom_tmul (s : S)
    (x : ArtinSchreierCover p R f) :
    artinSchreierCover_baseChangeHom p S f (s ⊗ₜ[R] x) =
      algebraMap S (ArtinSchreierCover p S (algebraMap R S f)) s *
        artinSchreierCover_baseMap p S f x := rfl

/-- Extending coefficients of the quotient gives the actual tensor product. -/
def artinSchreierCover_baseChangeEquiv :
    S ⊗[R] ArtinSchreierCover p R f ≃ₐ[S]
      ArtinSchreierCover p S (algebraMap R S f) := by
  refine AlgEquiv.ofAlgHom (artinSchreierCover_baseChangeHom p S f)
    (artinSchreierCover_baseChangeInv p S f) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change artinSchreierCover_baseChangeHom p S f
        (artinSchreierCover_baseChangeInv p S f
          (artinSchreierRoot p (algebraMap R S f))) =
      artinSchreierRoot p (algebraMap R S f)
    simp only [artinSchreierCover_baseChangeInv_root,
      artinSchreierCover_baseChangeHom_tmul, map_one, one_mul,
      artinSchreierCover_baseMap_root]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AdjoinRoot.algHom_ext
      change artinSchreierCover_baseChangeInv p S f
          (artinSchreierCover_baseChangeHom p S f (1 ⊗ₜ[R] artinSchreierRoot p f)) =
        1 ⊗ₜ[R] artinSchreierRoot p f
      simp only [artinSchreierCover_baseChangeHom_tmul, map_one, one_mul,
        artinSchreierCover_baseMap_root, artinSchreierCover_baseChangeInv_root]

@[simp] theorem artinSchreierCover_baseChangeEquiv_root :
    artinSchreierCover_baseChangeEquiv p S f (1 ⊗ₜ[R] artinSchreierRoot p f) =
      artinSchreierRoot p (algebraMap R S f) := by
  change artinSchreierCover_baseChangeHom p S f (1 ⊗ₜ[R] artinSchreierRoot p f) = _
  simp only [artinSchreierCover_baseChangeHom_tmul, map_one, one_mul,
    artinSchreierCover_baseMap_root]

@[simp] theorem artinSchreierCover_baseChangeEquiv_symm_root :
    (artinSchreierCover_baseChangeEquiv p S f).symm
        (artinSchreierRoot p (algebraMap R S f)) =
      1 ⊗ₜ[R] artinSchreierRoot p f :=
  artinSchreierCover_baseChangeInv_root p S f

#print axioms artinSchreierPolynomial_map
#print axioms artinSchreierCover_baseMap
#print axioms artinSchreierCover_baseMap_root
#print axioms artinSchreier_tensorRoot_relation
#print axioms artinSchreierCover_baseChangeHom
#print axioms artinSchreierCover_baseChangeInv
#print axioms artinSchreierCover_baseChangeInv_root
#print axioms artinSchreierCover_baseChangeHom_tmul
#print axioms artinSchreierCover_baseChangeEquiv
#print axioms artinSchreierCover_baseChangeEquiv_root
#print axioms artinSchreierCover_baseChangeEquiv_symm_root

end PrimeGap182.TypeIII
