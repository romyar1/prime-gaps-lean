import TypeIIIArtinSchreierStalkFunctions

/-!
# Fibers at field-valued points of an arbitrary affine base

For a compatible tower R → K → Ω, evaluation at the quotient generator
identifies homomorphisms from R[X]/(X^p-X-f) into Ω with the roots of
z^p-z=f(K).  Here R is any commutative ring; its map to K need not be
injective.  Composing with the spectrum comparison gives the actual
geometric fiber of the original cover over Spec R.

Algebraic closedness proves that this fiber has p points.  Its actual
free module is the function module on the root fiber, and the actual
deck map by a becomes precomposition by root translation by -a.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry
open scoped Classical

section QuotientFiber

variable (p : ℕ) (R K Ω : Type u) [CommRing R] [Field K] [Field Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] (f : R)

/-- Evaluation at the quotient generator produces a root with parameter
equal to the value of f at the given K-valued point. -/
def artinSchreierPointFiberOfHom (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    ArtinSchreierFiber p K Ω (algebraMap R K f) :=
  ⟨g (artinSchreierRoot p f), by
    have h := congrArg g (artinSchreierRoot_relation p f)
    simpa only [map_sub, map_pow, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R K Ω] using h⟩

/-- The literal quotient universal property turns each specialized root
into a homomorphism from the original R-algebra. -/
def artinSchreierPointHomOfFiber
    (z : ArtinSchreierFiber p K Ω (algebraMap R K f)) :
    ArtinSchreierCover p R f →ₐ[R] Ω :=
  AdjoinRoot.liftAlgHom (artinSchreierPolynomial p f) (Algebra.ofId R Ω) (z : Ω) (by
    simp only [artinSchreierPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change (z : Ω) ^ p - (z : Ω) - algebraMap R Ω f = 0
    rw [IsScalarTower.algebraMap_apply R K Ω]
    exact sub_eq_zero.mpr z.property)

/-- The original quotient's point fiber equals the specialized root fiber.
No injectivity of R → K or base-change comparison is assumed. -/
def artinSchreierPointHomEquivFiber :
    (ArtinSchreierCover p R f →ₐ[R] Ω) ≃
      ArtinSchreierFiber p K Ω (algebraMap R K f) where
  toFun := artinSchreierPointFiberOfHom p R K Ω f
  invFun := artinSchreierPointHomOfFiber p R K Ω f
  left_inv g := by
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root (artinSchreierPolynomial p f)
      (Algebra.ofId R Ω) (artinSchreierPointFiberOfHom p R K Ω f g : Ω) _
  right_inv z := by
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root (artinSchreierPolynomial p f)
      (Algebra.ofId R Ω) (z : Ω) _

@[simp] theorem artinSchreierPointHomEquivFiber_val
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    (artinSchreierPointHomEquivFiber p R K Ω f g : Ω) =
      g (artinSchreierRoot p f) := rfl

end QuotientFiber

section Characteristic

variable (p : ℕ) [Fact p.Prime] (R Ω : Type u) [CommRing R] [CharP R p]
  [Field Ω] [Algebra R Ω]

include R in
/-- A field-valued point of a characteristic-p ring retains that
characteristic, even when the point map has a nonzero kernel. -/
theorem artinSchreierPointField_charP : CharP Ω p := by
  let g : ZMod p →+* Ω :=
    (algebraMap R Ω).comp (ZMod.castHom (dvd_refl p) R)
  exact charP_of_injective_ringHom g.injective p

end Characteristic

section ActualSiteFiber

variable (p : ℕ) [Fact p.Prime] (R Ω : Type u) [CommRing R] [CharP R p]
  [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (f : R)

/-- The fiber of the original étale object on the small site of Spec R. -/
abbrev ArtinSchreierPointSiteFiber : Type u :=
  (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.obj
      (artinSchreierEtaleObject p f)

/-- The actual deck isomorphism acts as a permutation of that site fiber. -/
def artinSchreierPointSiteDeckEquiv (a : ZMod p) :
    ArtinSchreierPointSiteFiber p R Ω f ≃ ArtinSchreierPointSiteFiber p R Ω f :=
  ((Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.mapIso
      (artinSchreierEtaleDeckIso p f a)).toEquiv

@[simp] theorem artinSchreierPointSiteDeckEquiv_apply (a : ZMod p)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierPointSiteDeckEquiv p R Ω f a t =
      (Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
          (artinSchreierEtaleDeck p f a) t := rfl

variable (K : Type u) [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω]

/-- The actual site fiber over Spec R is the root fiber of the parameter
evaluated at its K-valued point. -/
def artinSchreierPointSiteEquivRoots :
    ArtinSchreierPointSiteFiber p R Ω f ≃
      ArtinSchreierFiber p K Ω (algebraMap R K f) :=
  (artinSchreierHomEquivEtaleFiber p f).symm.trans
    (artinSchreierPointHomEquivFiber p R K Ω f)

/-- The root coordinate still evaluates the original quotient generator. -/
@[simp] theorem artinSchreierPointSiteEquivRoots_val
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    (artinSchreierPointSiteEquivRoots p R Ω f K t : Ω) =
      (Spec.preimage t.left).hom (artinSchreierRoot p f) := rfl

variable [CharP Ω p] [Algebra (ZMod p) Ω]

omit [IsSepClosed Ω] in
/-- On quotient points the original R-algebra deck action is positive
translation of the specialized roots. -/
theorem artinSchreierPointHomEquivFiber_translation (a : ZMod p)
    (g : ArtinSchreierCover p R f →ₐ[R] Ω) :
    artinSchreierPointHomEquivFiber p R K Ω f
        (g.comp (artinSchreierCover_translationHom p f a)) =
      artinSchreierFiberTranslate p K Ω (algebraMap R K f) a
        (artinSchreierPointHomEquivFiber p R K Ω f g) := by
  apply Subtype.ext
  simp only [artinSchreierPointHomEquivFiber_val, AlgHom.comp_apply,
    artinSchreierCover_translationHom_root, map_add, AlgHom.commutes,
    artinSchreierFiberTranslate_val]
  have hc : (algebraMap R Ω).comp (ZMod.castHom (dvd_refl p) R) =
      algebraMap (ZMod p) Ω := Subsingleton.elim _ _
  exact congrArg (fun h : ZMod p →+* Ω => g (artinSchreierRoot p f) + h a) hc

/-- The actual site-functor action over Spec R agrees with root translation. -/
theorem artinSchreierPointSiteEquivRoots_deck (a : ZMod p)
    (t : ArtinSchreierPointSiteFiber p R Ω f) :
    artinSchreierPointSiteEquivRoots p R Ω f K
        ((Scheme.pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
            (artinSchreierEtaleDeck p f a) t) =
      artinSchreierFiberTranslate p K Ω (algebraMap R K f) a
        (artinSchreierPointSiteEquivRoots p R Ω f K t) := by
  change artinSchreierPointHomEquivFiber p R K Ω f
      ((artinSchreierHomEquivEtaleFiber p f).symm _) = _
  rw [artinSchreierHomEquivEtaleFiber_symm_deck]
  exact artinSchreierPointHomEquivFiber_translation p R Ω f K a
    ((artinSchreierHomEquivEtaleFiber p f).symm t)

/-- The inverse root coordinates intertwine the actual site permutation. -/
theorem artinSchreierPointSiteEquivRoots_symm_translate (a : ZMod p)
    (z : ArtinSchreierFiber p K Ω (algebraMap R K f)) :
    (Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
        (artinSchreierEtaleDeck p f a)
        ((artinSchreierPointSiteEquivRoots p R Ω f K).symm z) =
      (artinSchreierPointSiteEquivRoots p R Ω f K).symm
        (artinSchreierFiberTranslate p K Ω (algebraMap R K f) a z) := by
  apply (artinSchreierPointSiteEquivRoots p R Ω f K).injective
  rw [artinSchreierPointSiteEquivRoots_deck, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

end ActualSiteFiber

section FiniteFunctions

variable (p : ℕ) [Fact p.Prime] (R K Ω : Type u) [CommRing R] [CharP R p]
  [Field K] [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] (f : R)

include K in
/-- The actual site fiber over the original affine base has a point,
obtained from root existence over the algebraically closed field. -/
theorem artinSchreierPointSiteFiber_nonempty :
    Nonempty (ArtinSchreierPointSiteFiber p R Ω f) :=
  ⟨(artinSchreierPointSiteEquivRoots p R Ω f K).symm
    (artinSchreierGeometricRoot p K Ω (algebraMap R K f))⟩

variable [Algebra (ZMod p) Ω]

include K in
/-- The original cover has exactly p points in the specified geometric fiber. -/
theorem artinSchreierPointSiteFiber_card :
    Nat.card (ArtinSchreierPointSiteFiber p R Ω f) = p := by
  rw [Nat.card_congr (artinSchreierPointSiteEquivRoots p R Ω f K),
    artinSchreierFiber_card]

include K in
/-- The cardinality theorem discharges finiteness of the original site fiber. -/
theorem artinSchreierPointSiteFiber_finite :
    Finite (ArtinSchreierPointSiteFiber p R Ω f) :=
  Nat.finite_of_card_ne_zero (by
    rw [artinSchreierPointSiteFiber_card p R K Ω f]
    exact (Fact.out : p.Prime).ne_zero)

variable (E : Type u) [CommRing E]

/-- The actual free module on the original site's geometric fiber is the
function module on the specialized polynomial-root fiber. -/
def artinSchreierPointFreeEquivFunctions :
    (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f) ≃ₗ[E]
      (ArtinSchreierFiber p K Ω (algebraMap R K f) → E) := by
  letI := artinSchreierFiber_finite p K Ω (algebraMap R K f)
  exact (Finsupp.domLCongr (artinSchreierPointSiteEquivRoots p R Ω f K)).trans
    (Finsupp.linearEquivFunOnFinite E E
      (ArtinSchreierFiber p K Ω (algebraMap R K f)))

/-- Coefficients are read at the corresponding point of the original site. -/
@[simp] theorem artinSchreierPointFreeEquivFunctions_apply
    (v : (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f))
    (z : ArtinSchreierFiber p K Ω (algebraMap R K f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E v z =
      Finsupp.toFun (v : ArtinSchreierPointSiteFiber p R Ω f →₀ E)
        ((artinSchreierPointSiteEquivRoots p R Ω f K).symm z) := rfl

/-- The original cover's actual deck map pushes generators forward and
therefore acts on functions by the negative root translation. -/
theorem artinSchreierPointFreeEquivFunctions_deck_apply (a : ZMod p)
    (v : (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f))
    (z : ArtinSchreierFiber p K Ω (algebraMap R K f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        ((ModuleCat.free E).map
          ((Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
              (artinSchreierEtaleDeck p f a)) v) z =
      artinSchreierPointFreeEquivFunctions p R K Ω f E v
        (artinSchreierFiberTranslate p K Ω (algebraMap R K f) (-a) z) := by
  rw [artinSchreierPointFreeEquivFunctions_apply,
    artinSchreierPointFreeEquivFunctions_apply]
  let d := artinSchreierPointSiteDeckEquiv p R Ω f a
  have hi :
      d ((artinSchreierPointSiteEquivRoots p R Ω f K).symm
        (artinSchreierFiberTranslate p K Ω (algebraMap R K f) (-a) z)) =
        (artinSchreierPointSiteEquivRoots p R Ω f K).symm z := by
    rw [artinSchreierPointSiteDeckEquiv_apply,
      artinSchreierPointSiteEquivRoots_symm_translate,
      ← artinSchreierFiberTranslate_add, add_neg_cancel,
      artinSchreierFiberTranslate_zero]
  have h := Finsupp.mapDomain_apply d.injective v
    ((artinSchreierPointSiteEquivRoots p R Ω f K).symm
      (artinSchreierFiberTranslate p K Ω (algebraMap R K f) (-a) z))
  rw [hi] at h
  exact h

/-- The full function-space action retains the original base scheme. -/
theorem artinSchreierPointFreeEquivFunctions_deck (a : ZMod p)
    (v : (ModuleCat.free E).obj (ArtinSchreierPointSiteFiber p R Ω f)) :
    artinSchreierPointFreeEquivFunctions p R K Ω f E
        ((ModuleCat.free E).map
          ((Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).fiber.map
              (artinSchreierEtaleDeck p f a)) v) =
      fun z => artinSchreierPointFreeEquivFunctions p R K Ω f E v
        (artinSchreierFiberTranslate p K Ω (algebraMap R K f) (-a) z) := by
  funext z
  exact artinSchreierPointFreeEquivFunctions_deck_apply p R K Ω f E a v z

end FiniteFunctions

#print axioms artinSchreierPointFiberOfHom
#print axioms artinSchreierPointHomOfFiber
#print axioms artinSchreierPointHomEquivFiber
#print axioms artinSchreierPointHomEquivFiber_val
#print axioms artinSchreierPointField_charP
#print axioms ArtinSchreierPointSiteFiber
#print axioms artinSchreierPointSiteDeckEquiv
#print axioms artinSchreierPointSiteDeckEquiv_apply
#print axioms artinSchreierPointSiteEquivRoots
#print axioms artinSchreierPointSiteEquivRoots_val
#print axioms artinSchreierPointHomEquivFiber_translation
#print axioms artinSchreierPointSiteEquivRoots_deck
#print axioms artinSchreierPointSiteEquivRoots_symm_translate
#print axioms artinSchreierPointSiteFiber_nonempty
#print axioms artinSchreierPointSiteFiber_card
#print axioms artinSchreierPointSiteFiber_finite
#print axioms artinSchreierPointFreeEquivFunctions
#print axioms artinSchreierPointFreeEquivFunctions_apply
#print axioms artinSchreierPointFreeEquivFunctions_deck_apply
#print axioms artinSchreierPointFreeEquivFunctions_deck

end PrimeGap182.TypeIII
