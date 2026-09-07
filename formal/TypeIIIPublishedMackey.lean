import TypeIIIPublishedPhaseApplication
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# The cubic Mackey calculation from general finite-cover laws

The tensor, dual and finite direct sums here are actual finite-dimensional
representations.  The generic finite-cover laws are explicit parameters:
projection formula, duality, additivity and the restriction of a pushforward
as the sum of deck translates.  None asserts the decomposition of the
correlation representation.  The latter is derived below.

The intended realization is the tame cubic cover at infinity over the
algebraic closure of the generic direction field.  Fu, Proposition 0.8
(https://arxiv.org/pdf/math/0702436v5, p. 13), gives the rank-three
Kloosterman inertia model.  For n=3 with trivial multiplicative characters
its geometric tame twist is trivial.  Artin--Schreier tensor and dual rules
are stated on p. 2 of the same paper.  The cover rules are the ordinary
finite-etale projection formula and Galois base change; compare SGA 4,
XVII 5.2.9, cited explicitly by Fu on p. 23.  The operations must still be
realized by those actual functors.  They are not asserted for arbitrary
unrelated functions on representation objects.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Classical TensorProduct

namespace PrimeGap182.TypeIII.PublishedMackey

open PublishedPhaseApplication

universe u v w z t

variable {E : Type v} [Field E] {I : Type w} [Group I]

/-- The literal binary tensor representation. -/
def tensor (A B : FDRep E I) : FDRep E I := FDRep.of (Representation.tprod A.ρ B.ρ)

/-- Tensor an actual pair of equivariant linear equivalences. -/
def tensorEquiv {A B C D : FDRep E I}
    (f : Representation.Equiv A.ρ B.ρ) (g : Representation.Equiv C.ρ D.ρ) :
    Representation.Equiv (tensor A C).ρ (tensor B D).ρ where
  toLinearEquiv := TensorProduct.congr f.toLinearEquiv g.toLinearEquiv
  isIntertwining' h := by
    change TensorProduct.map f.toLinearMap g.toLinearMap ∘ₗ
        TensorProduct.map (A.ρ h) (C.ρ h) =
      TensorProduct.map (B.ρ h) (D.ρ h) ∘ₗ
        TensorProduct.map f.toLinearMap g.toLinearMap
    rw [← TensorProduct.map_comp, f.isIntertwining' h, g.isIntertwining' h,
      TensorProduct.map_comp]

/-- The contragredient of an actual equivariant equivalence. -/
def dualEquiv {A B : FDRep E I} (f : Representation.Equiv A.ρ B.ρ) :
    Representation.Equiv (dualRepresentation A).ρ (dualRepresentation B).ρ where
  toLinearEquiv := f.toLinearEquiv.symm.dualMap
  isIntertwining' h := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change (show Module.Dual E A.V from φ) (A.ρ h⁻¹ (f.symm x)) =
      (show Module.Dual E A.V from φ) (f.symm (B.ρ h⁻¹ x))
    congr 1
    exact (congrArg (fun k => k x) (f.symm.isIntertwining' h⁻¹)).symm

/-- Direct sum of actual equivariant linear equivalences. -/
def finiteSumEquiv {ι : Type} [Fintype ι] {A B : ι → FDRep E I}
    (f : ∀ i, Representation.Equiv (A i).ρ (B i).ρ) :
    Representation.Equiv (finiteSum A).ρ (finiteSum B).ρ where
  toLinearEquiv := DirectSum.congrLinearEquiv (fun i => (f i).toLinearEquiv)
  isIntertwining' h := by
    change DirectSum.lmap (fun i => (f i).toLinearMap) ∘ₗ
        DirectSum.lmap (fun i => (A i).ρ h) =
      DirectSum.lmap (fun i => (B i).ρ h) ∘ₗ
        DirectSum.lmap (fun i => (f i).toLinearMap)
    ext i x : 2
    simpa only [LinearMap.coe_comp, Function.comp_apply, DirectSum.lmap_lof] using
      congrArg (DirectSum.lof E ι (fun i => (B i).V) i)
        (congrArg (fun k => k x) ((f i).isIntertwining' h))

/-- The usual tensor/direct-sum distributivity map is equivariant for
the diagonal action.  This is proved, not a geometric hypothesis. -/
def tensorFiniteSumEquiv {ι : Type} [Fintype ι] (A : FDRep E I)
    (B : ι → FDRep E I) :
    Representation.Equiv (tensor A (finiteSum B)).ρ
      (finiteSum (fun i => tensor A (B i))).ρ where
  toLinearEquiv := TensorProduct.directSumRight E E A.V (fun i => (B i).V)
  isIntertwining' h := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply DirectSum.linearMap_ext
    intro i
    ext y
    change (TensorProduct.directSumRight E E A.V (fun j => (B j).V))
      (TensorProduct.map (A.ρ h) (DirectSum.lmap (fun j => (B j).ρ h))
        (x ⊗ₜ[E] DirectSum.lof E ι (fun j => (B j).V) i y)) =
      DirectSum.lmap (fun j => TensorProduct.map (A.ρ h) ((B j).ρ h))
        ((TensorProduct.directSumRight E E A.V (fun j => (B j).V))
          (x ⊗ₜ[E] DirectSum.lof E ι (fun j => (B j).V) i y))
    simp only [TensorProduct.map_tmul, DirectSum.lmap_lof,
      TensorProduct.directSumRight_tmul_lof]

variable {H : Type z} [Group H] {G : Type t} [Group G]

/-- An operation on actual finite-dimensional representations together
with its action on equivariant linear maps and the functor laws. -/
structure RepresentationFunctor (E : Type v) [Field E]
    (I : Type w) [Group I] (H : Type z) [Group H] where
  obj : FDRep E I → FDRep E H
  map : ∀ {A B : FDRep E I}, Representation.IntertwiningMap A.ρ B.ρ →
    Representation.IntertwiningMap (obj A).ρ (obj B).ρ
  map_id : ∀ A, map (Representation.IntertwiningMap.id A.ρ) =
    Representation.IntertwiningMap.id (obj A).ρ
  map_comp : ∀ {A B C : FDRep E I},
    ∀ f : Representation.IntertwiningMap A.ρ B.ρ,
    ∀ g : Representation.IntertwiningMap B.ρ C.ρ,
      map (g.comp f) = (map g).comp (map f)

/-- A functor with actual maps sends an equivariant equivalence to an
equivariant equivalence.  No separate isomorphism-preservation law is needed. -/
def RepresentationFunctor.mapEquiv (F : RepresentationFunctor E I H)
    {A B : FDRep E I} (f : Representation.Equiv A.ρ B.ρ) :
    Representation.Equiv (F.obj A).ρ (F.obj B).ρ := by
  have hleft : f.symm.toIntertwiningMap.comp f.toIntertwiningMap =
      Representation.IntertwiningMap.id A.ρ := by
    ext x
    exact f.toLinearEquiv.symm_apply_apply x
  have hright : f.toIntertwiningMap.comp f.symm.toIntertwiningMap =
      Representation.IntertwiningMap.id B.ρ := by
    ext x
    exact f.toLinearEquiv.apply_symm_apply x
  have hl := congrArg (fun h => h.toLinearMap) (F.map_comp
    f.toIntertwiningMap f.symm.toIntertwiningMap)
  have hr := congrArg (fun h => h.toLinearMap) (F.map_comp
    f.symm.toIntertwiningMap f.toIntertwiningMap)
  rw [hleft, F.map_id] at hl
  rw [hright, F.map_id] at hr
  exact {
    toLinearEquiv := LinearEquiv.ofLinearMap
      (F.map f.toIntertwiningMap).toLinearMap
      (F.map f.symm.toIntertwiningMap).toLinearMap hr.symm hl.symm
    isIntertwining' := (F.map f.toIntertwiningMap).isIntertwining' }

variable {L : Type u} [Field L]

/-- Geometric cubic-cover operations and its three deck-coordinate
multipliers.  Their maps are actual equivariant maps.  The intended base
field is algebraically closed and has characteristic different from three. -/
structure CubicCoverData (L : Type u) [Field L] (E : Type v) [Field E]
    (I : Type w) [Group I] (H : Type z) [Group H] where
  push : RepresentationFunctor E H I
  pull : RepresentationFunctor E I H
  deck : Fin 3 → RepresentationFunctor E H H
  zeta : Fin 3 → L
  zeta_cube : ∀ i, zeta i ^ 3 = 1
  zeta_injective : Function.Injective zeta

/-- General finite-etale-cover identities.  The Galois base-change
formula is stated for an arbitrary representation on the covering field,
not for Kloosterman sheaves or the correlation tensor. -/
structure CubicCoverRules (P : CubicCoverData L E I H) where
  projection : ∀ A : FDRep E H, ∀ B : FDRep E I,
    Representation.Equiv (tensor (P.push.obj A) B).ρ
      (P.push.obj (tensor A (P.pull.obj B))).ρ
  dual : ∀ A : FDRep E H,
    Representation.Equiv (dualRepresentation (P.push.obj A)).ρ
      (P.push.obj (dualRepresentation A)).ρ
  sum : ∀ {ι : Type} [Fintype ι], ∀ A : ι → FDRep E H,
    Representation.Equiv (P.push.obj (finiteSum A)).ρ
      (finiteSum (fun i => P.push.obj (A i))).ρ
  galois : ∀ A : FDRep E H,
    Representation.Equiv (P.pull.obj (P.push.obj A)).ρ
      (finiteSum (fun i => (P.deck i).obj A)).ρ

/-- The Artin--Schreier representation for the linear polynomial c*x
on the covering local field. -/
structure LinearASData (L : Type u) [Field L] (E : Type v) [Field E]
    (H : Type z) [Group H] where
  phase : L → FDRep E H

/-- The usual character tensor, dual, and coordinate-pullback rules.
Fu p. 2 recalls the first two; deck pullback substitutes x ↦ ζ*x. -/
structure LinearASRules (P : CubicCoverData L E I H) (A : LinearASData L E H) where
  tensor : ∀ a b : L, Representation.Equiv
    (PublishedMackey.tensor (A.phase a) (A.phase b)).ρ (A.phase (a + b)).ρ
  dual : ∀ a : L, Representation.Equiv
    (dualRepresentation (A.phase a)).ρ (A.phase (-a)).ρ
  deck : ∀ i : Fin 3, ∀ a : L, Representation.Equiv
    ((P.deck i).obj (A.phase a)).ρ (A.phase (a * P.zeta i)).ρ

/-- The geometric infinity restrictions of the rank-three Kloosterman
sheaf after the scalar pullback x ↦ λ*x.  It is separate realization data. -/
structure KloostermanInfinityData (L : Type u) [Field L] (E : Type v) [Field E]
    (I : Type w) [Group I] where
  kl : L → FDRep E I

/-- Fu Proposition 0.8 for n=3 and trivial multiplicative characters,
followed by the scalar base change x ↦ λ*x, lifted as x ↦ r*x.
This law concerns a single Kloosterman sheaf and arbitrary nonzero r;
it does not contain a correlation or a tensor decomposition. -/
structure KloostermanInfinityRules [IsAlgClosed L] [CharZero E]
    (p : ℕ) [Fact p.Prime] [CharP L p]
    (P : CubicCoverData L E I H) (A : LinearASData L E H)
    (K : KloostermanInfinityData L E I) where
  model : 3 < p → ∀ c r : L, r ≠ 0 → r ^ 3 = c →
    Representation.Equiv (K.kl c).ρ (P.push.obj (A.phase (3 * r))).ρ

/-- Mackey decomposition for arbitrary linear characters, deduced from
the four generic finite-cover identities and the Artin--Schreier laws.
The proof composes actual equivariant equivalences. -/
def inducedAS_tensor_dual (P : CubicCoverData L E I H) (A : LinearASData L E H)
    (PR : CubicCoverRules P) (AR : LinearASRules P A) (a b : L) :
    Representation.Equiv
      (tensor (P.push.obj (A.phase a)) (dualRepresentation (P.push.obj (A.phase b)))).ρ
      (finiteSum (fun i => P.push.obj (A.phase (a - b * P.zeta i)))).ρ := by
  let B : Fin 3 → FDRep E H := fun i => (P.deck i).obj (dualRepresentation (A.phase b))
  let ebranch (i : Fin 3) : Representation.Equiv
      (tensor (A.phase a) (B i)).ρ (A.phase (a - b * P.zeta i)).ρ := by
    have ed := ((P.deck i).mapEquiv (AR.dual b)).trans (AR.deck i (-b))
    have et := (tensorEquiv (Representation.Equiv.refl (A.phase a).ρ) ed).trans
      (AR.tensor a (-b * P.zeta i))
    rw [show a + -b * P.zeta i = a - b * P.zeta i by ring] at et
    exact et
  exact (tensorEquiv (Representation.Equiv.refl (P.push.obj (A.phase a)).ρ)
      (PR.dual (A.phase b))).trans <|
    (PR.projection (A.phase a) (P.push.obj (dualRepresentation (A.phase b)))).trans <|
    (P.push.mapEquiv (tensorEquiv (Representation.Equiv.refl (A.phase a).ρ)
      (PR.galois (dualRepresentation (A.phase b))))).trans <|
    (P.push.mapEquiv (tensorFiniteSumEquiv (A.phase a) B)).trans <|
    (P.push.mapEquiv (finiteSumEquiv ebranch)).trans <|
    PR.sum (fun i => A.phase (a - b * P.zeta i))

/-- The three actual cubic branches determined by a single chosen root. -/
def cubicBranch (P : CubicCoverData L E I H) (r : L) (i : Fin 3) : L := r * P.zeta i

theorem cubicBranch_cube (P : CubicCoverData L E I H) (c r : L)
    (hr : r ^ 3 = c) (i : Fin 3) : cubicBranch P r i ^ 3 = c := by
  rw [cubicBranch, mul_pow, hr, P.zeta_cube, mul_one]

theorem cubicBranch_injective (P : CubicCoverData L E I H) (r : L) (hr : r ≠ 0) :
    Function.Injective (cubicBranch P r) := by
  intro i j hij
  apply P.zeta_injective
  exact mul_left_cancel₀ hr hij

/-- The rank-nine correlation infinity representation decomposes into
the three cubic pushforwards.  This is the family-specific conclusion,
derived here from Fu's single-Kloosterman model and the generic cover laws. -/
def kloosterman_correlation_mackey [IsAlgClosed L] [CharZero E]
    (p : ℕ) [Fact p.Prime] [CharP L p]
    (P : CubicCoverData L E I H) (A : LinearASData L E H)
    (K : KloostermanInfinityData L E I)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (KR : KloostermanInfinityRules p P A K) (hp : 3 < p)
    (c r : L) (hr : r ≠ 0) (hcube : r ^ 3 = c) :
    Representation.Equiv (tensor (K.kl 1) (dualRepresentation (K.kl c))).ρ
      (finiteSum (fun i => P.push.obj (A.phase (3 * (1 - cubicBranch P r i))))).ρ := by
  have eone : Representation.Equiv (K.kl 1).ρ (P.push.obj (A.phase 3)).ρ := by
    have e := KR.model hp 1 1 one_ne_zero (one_pow 3)
    rw [mul_one] at e
    exact e
  have e := (tensorEquiv eone (dualEquiv (KR.model hp c r hr hcube))).trans
    (inducedAS_tensor_dual P A PR AR 3 (3 * r))
  have heq : (fun i => P.push.obj (A.phase (3 * (1 - cubicBranch P r i)))) =
      (fun i => P.push.obj (A.phase (3 - 3 * r * P.zeta i))) := by
    funext i
    have hscalar : 3 * (1 - cubicBranch P r i) = 3 - 3 * r * P.zeta i := by
      dsimp only [cubicBranch]
      ring
    rw [hscalar]
  rw [heq]
  exact e

end PrimeGap182.TypeIII.PublishedMackey

#print axioms PrimeGap182.TypeIII.PublishedMackey.tensor
#print axioms PrimeGap182.TypeIII.PublishedMackey.tensorEquiv
#print axioms PrimeGap182.TypeIII.PublishedMackey.dualEquiv
#print axioms PrimeGap182.TypeIII.PublishedMackey.finiteSumEquiv
#print axioms PrimeGap182.TypeIII.PublishedMackey.tensorFiniteSumEquiv
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.mapEquiv
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules
#print axioms PrimeGap182.TypeIII.PublishedMackey.inducedAS_tensor_dual
#print axioms PrimeGap182.TypeIII.PublishedMackey.cubicBranch
#print axioms PrimeGap182.TypeIII.PublishedMackey.cubicBranch_cube
#print axioms PrimeGap182.TypeIII.PublishedMackey.cubicBranch_injective
#print axioms PrimeGap182.TypeIII.PublishedMackey.kloosterman_correlation_mackey

/- Generated declarations are included in the axiom audit. -/
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.deck
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.pull
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.push
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.zeta
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.zeta_cube
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverData.zeta_injective
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.dual
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.galois
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.projection
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.CubicCoverRules.sum
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.kl
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityData.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.model
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.KloostermanInfinityRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.phase
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASData.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.deck
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.dual
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.LinearASRules.tensor
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.casesOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.map
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.map_comp
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.map_id
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.mk
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.obj
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.rec
#print axioms PrimeGap182.TypeIII.PublishedMackey.RepresentationFunctor.recOn
#print axioms PrimeGap182.TypeIII.PublishedMackey.cubicBranch.eq_1
