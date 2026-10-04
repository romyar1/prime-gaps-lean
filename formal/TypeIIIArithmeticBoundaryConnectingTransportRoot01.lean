import Mathlib.Algebra.Category.ModuleCat.Basic

noncomputable section
open CategoryTheory
namespace PrimeGap182.TypeIII.ArithmeticBoundaryConnectingTransportRoot01

universe u v
variable {C : Type u} [Category.{v} C]
  {Bnative Cnative Bstandard Cstandard : C}

/-- Transport the independently constructed standard connecting morphism through
individual boundary-invariant and compact-fiber comparisons. -/
def transport (iB : Bnative ≅ Bstandard) (iC : Cnative ≅ Cstandard)
    (δ : Bstandard ⟶ Cstandard) : Bnative ⟶ Cnative :=
  iB.hom ≫ δ ≫ iC.inv

/-- Frobenius equivariance follows from the two individual comparison squares
and standard connecting-map naturality. No native connecting map is an input. -/
theorem frobenius_square (iB : Bnative ≅ Bstandard) (iC : Cnative ≅ Cstandard)
    (δ : Bstandard ⟶ Cstandard)
    (τB : Bnative ⟶ Bnative) (τC : Cnative ⟶ Cnative)
    (σB : Bstandard ⟶ Bstandard) (σC : Cstandard ⟶ Cstandard)
    (hB : τB ≫ iB.hom = iB.hom ≫ σB)
    (hC : τC ≫ iC.hom = iC.hom ≫ σC)
    (hδ : σB ≫ δ = δ ≫ σC) :
    τB ≫ transport iB iC δ = transport iB iC δ ≫ τC := by
  have hiCinv : σC ≫ iC.inv = iC.inv ≫ τC := by
    apply (cancel_mono iC.hom).1
    calc
      (σC ≫ iC.inv) ≫ iC.hom = σC := by simp
      _ = (iC.inv ≫ τC) ≫ iC.hom := by
        rw [Category.assoc, hC, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    τB ≫ transport iB iC δ = (τB ≫ iB.hom) ≫ δ ≫ iC.inv := by
      simp only [transport, Category.assoc]
    _ = iB.hom ≫ (σB ≫ δ) ≫ iC.inv := by
      rw [hB]
      simp only [Category.assoc]
    _ = iB.hom ≫ δ ≫ (σC ≫ iC.inv) := by
      rw [hδ]
      simp only [Category.assoc]
    _ = transport iB iC δ ≫ τC := by
      rw [hiCinv]
      simp only [transport, Category.assoc]

variable {R : Type} [Ring R]
  {BN CN BS CS : ModuleCat.{0} R}

/-- Literal linear-map evaluation of the computed connecting morphism. -/
theorem transport_apply (iB : BN ≅ BS) (iC : CN ≅ CS) (δ : BS ⟶ CS) (z : BN) :
    (transport iB iC δ).hom z = iC.inv.hom (δ.hom (iB.hom.hom z)) := rfl

/-- The pointwise form required by the arithmetic boundary-input interface. -/
theorem frobenius_square_apply (iB : BN ≅ BS) (iC : CN ≅ CS) (δ : BS ⟶ CS)
    (τB : BN ⟶ BN) (τC : CN ⟶ CN) (σB : BS ⟶ BS) (σC : CS ⟶ CS)
    (hB : τB ≫ iB.hom = iB.hom ≫ σB)
    (hC : τC ≫ iC.hom = iC.hom ≫ σC)
    (hδ : σB ≫ δ = δ ≫ σC) (z : BN) :
    (transport iB iC δ).hom (τB.hom z) = τC.hom ((transport iB iC δ).hom z) := by
  change (τB ≫ transport iB iC δ).hom z = (transport iB iC δ ≫ τC).hom z
  exact congrArg (fun f : BN ⟶ CN => f.hom z) (frobenius_square iB iC δ τB τC σB σC hB hC hδ)

end PrimeGap182.TypeIII.ArithmeticBoundaryConnectingTransportRoot01
