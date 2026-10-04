import TypeIIIOriginStalksFromStandardWeilInvariants01

/-! Independent standard primitive sheaf operations, and GENERAL published
theorems on every genuinely interpreted package. The prescribed interpretation
means continuous constructible Qbar2 sheaves, actual affine/Gm restriction and
ordinary geometric point pull, fixed Qbar2-to-C scalar extension, the raw
untwisted Kl_n convolution construction, and the Lang 1-F associated sheaf.
It reads S/B/P only. Its existence and native realization are external cuts.

Katz GKM 7.4.3 gives identity on raw Kl_n INVARIANTS, not its whole nearby
representation. Section 4.3 gives the ALL-point scalar action on the Lang
rank-one sheaf. The lisse ordinary stalk/inertia comparison is separate.
No OriginStalks, native source rule, or completed provider is a premise. -/
noncomputable section
open CategoryTheory
namespace PrimeGap182.TypeIII.StandardKloostermanLangOrigin
open StandardGmTraceFromFaithfulArithmeticOperations StandardP1BoundaryPrimitives
open OriginStalksFromStandardWeilInvariants TwoAdicComplexEmbedding
universe nu

/-- Independently standard affine, point and primitive-construction operators.
The raw Kl_n is the untwisted rank-n construction with all multiplicative
characters trivial. AS uses Katz's Lang 1-F convention and character psi. -/
structure Operations (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S) where
  Affine : ∀ (E : Type) [Field E] [Fintype E], (2 : E) ≠ 0 → Type
  [affineCategory : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Category.{nu} (Affine E h2)]
  restriction : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Affine E h2 ⥤ S.Curve E h2
  point : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    E → Affine E h2 ⥤ S.Spec E h2
  Lisse : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    Affine E h2 → Prop
  rawKloosterman : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    ℕ → AddChar E (PadicAlgCl 2) → S.Curve E h2
  langAS : ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0),
    AddChar E (PadicAlgCl 2) → Affine E h2

attribute [instance] Operations.affineCategory
variable {S : StandardGmPrimitives.{nu}} (B : Primitives.{nu,0,0} S)
  (P : Operations S B) (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)

def pointFiber (A : P.Affine E h2) (a : E) : ModuleCat.{0} ℂ :=
  (S.fiber E h2).obj ((P.point E h2 a).obj A)

def pointFrobenius (A : P.Affine E h2) (a : E) :
    pointFiber B P E h2 A a →ₗ[ℂ] pointFiber B P E h2 A a :=
  ((S.geometricFrobenius E h2).app ((P.point E h2 a).obj A)).hom

/-- GENERAL published results, fixed before the prime, source parameters and
native realization. Ordinary stalk comparison is guarded by lissity; neither
the full raw Kl_n Frobenius nor a native formula is asserted. -/
structure PublishedTheorems
    (interpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
      Operations S B → Prop) : Prop where
  rawInvariant : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S)
    (P : Operations S B), interpretation S B P →
    ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (n : ℕ), 0 < n → ∀ (psi : AddChar E (PadicAlgCl 2)), psi ≠ 1 →
      ∀ x, (invariantStalks (B.origin E h2) (B.originConjugation E h2)
        (B.originWeil E h2)).frobenius (P.rawKloosterman E h2 n psi) x = x
  langLisse : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S)
    (P : Operations S B), interpretation S B P →
    ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (psi : AddChar E (PadicAlgCl 2)), P.Lisse E h2 (P.langAS E h2 psi)
  ordinaryStalk : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S)
    (P : Operations S B), interpretation S B P →
    ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (A : P.Affine E h2), P.Lisse E h2 A →
      ∃ e : (invariantStalks (B.origin E h2) (B.originConjugation E h2)
        (B.originWeil E h2)).fiber ((P.restriction E h2).obj A) ≃ₗ[ℂ]
          pointFiber B P E h2 A 0,
        ∀ x, e ((invariantStalks (B.origin E h2) (B.originConjugation E h2)
          (B.originWeil E h2)).frobenius ((P.restriction E h2).obj A) x) =
          pointFrobenius B P E h2 A 0 (e x)
  langPoint : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S)
    (P : Operations S B), interpretation S B P →
    ∀ (E : Type) [Field E] [Fintype E] (h2 : (2 : E) ≠ 0)
      (psi : AddChar E (PadicAlgCl 2)) (a : E),
      ∃ e : pointFiber B P E h2 (P.langAS E h2 psi) a ≃ₗ[ℂ] ℂ,
        ∀ x, e (pointFrobenius B P E h2 (P.langAS E h2 psi) a x) =
          complexEquiv (psi a) * e x

variable {interpretation : ∀ (S : StandardGmPrimitives.{nu}) (B : Primitives.{nu,0,0} S),
    Operations S B → Prop}
  (published : PublishedTheorems interpretation) (model : interpretation S B P)

include published model

/-- Raw untwisted Kl_n, for every positive n; only invariant vectors. -/
theorem raw_invariant_frobenius (n : ℕ) (hn : 0 < n)
    (psi : AddChar E (PadicAlgCl 2)) (hpsi : psi ≠ 1)
    (x : (invariantStalks (B.origin E h2) (B.originConjugation E h2)
      (B.originWeil E h2)).fiber (P.rawKloosterman E h2 n psi)) :
    (invariantStalks (B.origin E h2) (B.originConjugation E h2)
      (B.originWeil E h2)).frobenius (P.rawKloosterman E h2 n psi) x = x :=
  published.rawInvariant S B P model E h2 n hn psi hpsi x

/-- The ALL-point Lang law specializes at zero by psi(0)=1, with no
rank-one trace-to-action inference and no finite-torsion-to-C map. -/
theorem lang_zero_point_frobenius (psi : AddChar E (PadicAlgCl 2))
    (x : pointFiber B P E h2 (P.langAS E h2 psi) 0) :
    pointFrobenius B P E h2 (P.langAS E h2 psi) 0 x = x := by
  obtain ⟨e, he⟩ := published.langPoint S B P model E h2 psi 0
  apply e.injective
  simpa only [AddChar.map_zero_eq_one, map_one, one_mul] using he x

/-- Ordinary lisse point/inertia compatibility transports the zero action
to SAME chosen Weil Frobenius on the whole invariant subspace. -/
theorem lang_invariant_frobenius (psi : AddChar E (PadicAlgCl 2))
    (x : (invariantStalks (B.origin E h2) (B.originConjugation E h2)
      (B.originWeil E h2)).fiber ((P.restriction E h2).obj (P.langAS E h2 psi))) :
    (invariantStalks (B.origin E h2) (B.originConjugation E h2)
      (B.originWeil E h2)).frobenius
        ((P.restriction E h2).obj (P.langAS E h2 psi)) x = x := by
  obtain ⟨e, he⟩ := published.ordinaryStalk S B P model E h2 (P.langAS E h2 psi)
    (published.langLisse S B P model E h2 psi)
  apply e.injective
  rw [he, lang_zero_point_frobenius B P E h2 published model]

end PrimeGap182.TypeIII.StandardKloostermanLangOrigin
