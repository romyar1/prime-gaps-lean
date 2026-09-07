import TypeIIIArtinSchreierBaseChange
import TypeIIIArtinSchreierSplitting

/-!
# The actual Artin--Schreier torsor isomorphism

After base change by the Artin--Schreier cover itself, the second copy
has the distinguished root of the first copy. The ring splitting theorem
therefore gives an isomorphism from the tensor square to `p` copies of the
cover algebra. Its component indexed by `a` sends `x ⊗ y` to `x τₐ(y)`.
This proves the torsor identity for the actual coordinate rings, including
when the cover algebra has zero divisors.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] (f : R)

/-- The base ring injects into the monic quotient of positive degree. -/
theorem artinSchreierCover_algebraMap_injective :
    Function.Injective (algebraMap R (ArtinSchreierCover p R f)) := by
  let : Nontrivial R := artinSchreierBase_nontrivial p
  apply AdjoinRoot.of.injective_of_monic_of_degree_pos
    (artinSchreierPolynomial_monic p f)
  rw [← Polynomial.natDegree_pos_iff_degree_pos, artinSchreierPolynomial_natDegree]
  exact (Fact.out : p.Prime).pos

/-- The actual quotient retains the exact prime characteristic. -/
theorem artinSchreierCover_charP : CharP (ArtinSchreierCover p R f) p :=
  charP_of_injective_algebraMap (artinSchreierCover_algebraMap_injective p f) p

attribute [local instance] artinSchreierCover_charP

/-- The cover is trivial over itself: its tensor square is the product
indexed by the additive prime field. -/
def artinSchreierCover_torsorEquiv :
    ArtinSchreierCover p R f ⊗[R] ArtinSchreierCover p R f ≃ₐ[ArtinSchreierCover p R f]
      (ZMod p → ArtinSchreierCover p R f) :=
  (artinSchreierCover_baseChangeEquiv p (ArtinSchreierCover p R f) f).trans
    (artinSchreierCover_splitEquiv p (ArtinSchreierCover p R f)
      (algebraMap R (ArtinSchreierCover p R f) f) (artinSchreierRoot p f)
      (artinSchreierRoot_relation p f))

/-- On the second distinguished root the component is exactly translation. -/
@[simp] theorem artinSchreierCover_torsorEquiv_rightRoot (a : ZMod p) :
    artinSchreierCover_torsorEquiv p f (1 ⊗ₜ[R] artinSchreierRoot p f) a =
      artinSchreierRoot p f + ZMod.castHom (dvd_refl p) (ArtinSchreierCover p R f) a := by
  simp only [artinSchreierCover_torsorEquiv, AlgEquiv.trans_apply,
    artinSchreierCover_baseChangeEquiv_root, artinSchreierCover_splitEquiv_root]

/-- Each component fixes the first copy of the coordinate ring. -/
@[simp] theorem artinSchreierCover_torsorEquiv_left (x : ArtinSchreierCover p R f)
    (a : ZMod p) :
    artinSchreierCover_torsorEquiv p f (x ⊗ₜ[R] 1) a = x := by
  change artinSchreierCover_torsorEquiv p f
    (algebraMap (ArtinSchreierCover p R f)
      (ArtinSchreierCover p R f ⊗[R] ArtinSchreierCover p R f) x) a = x
  rw [(artinSchreierCover_torsorEquiv p f).commutes]
  rfl

/-- The explicit component of the torsor map, formed from multiplication
and the actual quotient deck translation. -/
def artinSchreierCover_torsorComponent (a : ZMod p) :
    ArtinSchreierCover p R f ⊗[R] ArtinSchreierCover p R f →ₐ[ArtinSchreierCover p R f]
      ArtinSchreierCover p R f :=
  Algebra.TensorProduct.lift (AlgHom.id _ _)
    (artinSchreierCover_translationHom p f a) (fun _ _ => Commute.all _ _)

/-- The constructed product isomorphism is the canonical torsor map,
not merely some isomorphism of rings of the same rank. -/
theorem artinSchreierCover_torsorEquiv_component (a : ZMod p) :
    (Pi.evalAlgHom (ArtinSchreierCover p R f)
      (fun _ : ZMod p => ArtinSchreierCover p R f) a).comp
        (artinSchreierCover_torsorEquiv p f).toAlgHom =
      artinSchreierCover_torsorComponent p f a := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AdjoinRoot.algHom_ext
    change artinSchreierCover_torsorEquiv p f (1 ⊗ₜ[R] artinSchreierRoot p f) a =
      1 * artinSchreierCover_translationHom p f a (artinSchreierRoot p f)
    rw [one_mul, artinSchreierCover_torsorEquiv_rightRoot,
      artinSchreierCover_translationHom_root]
    congr 1
    have hc : ZMod.castHom (dvd_refl p) (ArtinSchreierCover p R f) =
        (algebraMap R (ArtinSchreierCover p R f)).comp (ZMod.castHom (dvd_refl p) R) :=
      Subsingleton.elim _ _
    exact congrArg (fun g : ZMod p →+* ArtinSchreierCover p R f => g a) hc

/-- The actual torsor isomorphism has component `x τₐ(y)` on pure tensors. -/
@[simp] theorem artinSchreierCover_torsorEquiv_tmul
    (x y : ArtinSchreierCover p R f) (a : ZMod p) :
    artinSchreierCover_torsorEquiv p f (x ⊗ₜ[R] y) a =
      x * artinSchreierCover_translationHom p f a y :=
  AlgHom.congr_fun (artinSchreierCover_torsorEquiv_component p f a) (x ⊗ₜ[R] y)

#print axioms artinSchreierCover_algebraMap_injective
#print axioms artinSchreierCover_charP
#print axioms artinSchreierCover_torsorEquiv
#print axioms artinSchreierCover_torsorEquiv_rightRoot
#print axioms artinSchreierCover_torsorEquiv_left
#print axioms artinSchreierCover_torsorComponent
#print axioms artinSchreierCover_torsorEquiv_component
#print axioms artinSchreierCover_torsorEquiv_tmul

end PrimeGap182.TypeIII
