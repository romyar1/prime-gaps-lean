import TypeIIIKloostermanBocksteinTransitions
import TypeIIIKloostermanFiniteBockstein
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# The original Bockstein exact sequence of inverse systems

The actual finite-category connecting maps are natural for the original
independently defined finite transitions. Their targets form a tower
with constant object and complementary-power transition maps. Together
with the original scalar and reduction maps, this gives three consecutive
exact triples in the actual category of sheaf-valued inverse systems.

The power towers and the constant towers have different transition maps.
No inverse limit is taken, and no adic cohomology comparison is asserted.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

/-- Actual evaluation functors detect exactness of a short complex in
an abelian functor category. -/
theorem functorShortComplex_exact_iff_eval
    {J C : Type*} [Category* J] [Category* C] [Abelian C]
    (S : ShortComplex (J ⥤ C)) :
    S.Exact ↔ ∀ j : J, (S.map ((evaluation J C).obj j)).Exact := by
  have hE : JointlyReflectIsomorphisms (fun j : J => (evaluation J C).obj j) := by
    constructor
    intro X Y α hα
    have : ∀ j : J, IsIso (α.app j) := fun j => hα j
    exact NatIso.isIso_of_isIso_app α
  exact hE.exact_iff S

attribute [local instance] kloostermanPhaseRing_charP HasDerivedCategory.standard

variable (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)

/-- The canonical finite-category connecting maps are natural for the
original independently defined restricted finite reductions. -/
theorem kloostermanFiniteBocksteinConnecting_naturality
    (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    kloostermanFiniteCoefficientRestrictedReduction p ell hne d hmn ≫
        kloostermanFiniteBocksteinConnecting p ell hne d m =
      kloostermanFiniteBocksteinConnecting p ell hne d n ≫
        ((ell ^ (n - m)) • 𝟙 (kloostermanLimitDerivedImage p ell hne (d + 1))) := by
  rw [kloostermanFiniteBocksteinConnecting, ← assoc,
    kloostermanFiniteCoefficientRestrictedReduction_toTower, assoc,
    kloostermanBocksteinConnecting_naturality, ← assoc]
  rfl

/-- The actual complementary-power tower on the ordinary derived image.
Every object is H_d, and the transition n to m multiplies by ell^(n-m). -/
def kloostermanBocksteinPowerTower (d : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (Spec (.of (Polynomial (ZMod p)))).smallEtaleTopology
      (ModuleCat.{0} (TorsionCoefficientLimit p ell)) where
  obj _ := kloostermanLimitDerivedImage p ell hne d
  map {n m} _ := (ell ^ (n.unop - m.unop)) •
    𝟙 (kloostermanLimitDerivedImage p ell hne d)
  map_id n := by
    rw [Nat.sub_self, pow_zero, one_nsmul]
  map_comp {n m k} g h := by
    simp only [Preadditive.comp_nsmul, Category.comp_id]
    rw [← mul_smul, ← pow_add]
    congr 2
    have hmn := leOfHom g.unop
    have hkm := leOfHom h.unop
    omega

/-- Every power-tower object is the original ordinary derived image. -/
@[simp] theorem kloostermanBocksteinPowerTower_obj (d : ℕ) (n : ℕᵒᵖ) :
    (kloostermanBocksteinPowerTower p ell hne d).obj n =
      kloostermanLimitDerivedImage p ell hne d := rfl

/-- The power-tower map is the stated literal integer multiplication. -/
@[simp] theorem kloostermanBocksteinPowerTower_map
    (d : ℕ) {n m : ℕᵒᵖ} (g : n ⟶ m) :
    (kloostermanBocksteinPowerTower p ell hne d).map g =
      (ell ^ (n.unop - m.unop)) • 𝟙 (kloostermanLimitDerivedImage p ell hne d) := rfl

/-- The level-n coefficient power defines a natural map from the
actual power tower to the constant ordinary derived image. -/
def kloostermanBocksteinScalarSystem (d : ℕ) :
    kloostermanBocksteinPowerTower p ell hne d ⟶
      (Functor.const ℕᵒᵖ).obj (kloostermanLimitDerivedImage p ell hne d) where
  app n := (ell ^ (n.unop + 1)) • 𝟙 (kloostermanLimitDerivedImage p ell hne d)
  naturality {n m} g := by
    change ((ell ^ (n.unop - m.unop)) •
        𝟙 (kloostermanLimitDerivedImage p ell hne d)) ≫
      ((ell ^ (m.unop + 1)) • 𝟙 (kloostermanLimitDerivedImage p ell hne d)) =
      ((ell ^ (n.unop + 1)) • 𝟙 (kloostermanLimitDerivedImage p ell hne d)) ≫ 𝟙 _
    simp only [Preadditive.comp_nsmul, Category.comp_id]
    rw [← mul_smul, ← pow_add]
    congr 2
    have hmn := leOfHom g.unop
    omega

/-- The original finite-category reductions give the actual natural
map from the constant ordinary derived image to the original finite tower. -/
def kloostermanBocksteinReductionSystem (d : ℕ) :
    (Functor.const ℕᵒᵖ).obj (kloostermanLimitDerivedImage p ell hne d) ⟶
      kloostermanFiniteCoefficientDerivedTower p ell hne d where
  app n := kloostermanFiniteBocksteinReduction p ell hne d n.unop
  naturality {n m} g := by
    change 𝟙 _ ≫ kloostermanFiniteBocksteinReduction p ell hne d m.unop =
      kloostermanFiniteBocksteinReduction p ell hne d n.unop ≫
        kloostermanFiniteCoefficientRestrictedReduction p ell hne d (leOfHom g.unop)
    rw [id_comp, kloostermanFiniteBocksteinReduction_comp]

/-- The original finite-category connecting maps form a natural
transformation to the next-degree complementary-power tower. -/
def kloostermanBocksteinConnectingSystem (d : ℕ) :
    kloostermanFiniteCoefficientDerivedTower p ell hne d ⟶
      kloostermanBocksteinPowerTower p ell hne (d + 1) where
  app n := kloostermanFiniteBocksteinConnecting p ell hne d n.unop
  naturality {_n _m} g :=
    kloostermanFiniteBocksteinConnecting_naturality p ell hne d (leOfHom g.unop)

/-- Scalar components retain the original coefficient powers. -/
@[simp] theorem kloostermanBocksteinScalarSystem_app (d : ℕ) (n : ℕᵒᵖ) :
    (kloostermanBocksteinScalarSystem p ell hne d).app n =
      (ell ^ (n.unop + 1)) • 𝟙 (kloostermanLimitDerivedImage p ell hne d) := rfl

/-- Reduction components are the original finite-category reduction maps. -/
@[simp] theorem kloostermanBocksteinReductionSystem_app (d : ℕ) (n : ℕᵒᵖ) :
    (kloostermanBocksteinReductionSystem p ell hne d).app n =
      kloostermanFiniteBocksteinReduction p ell hne d n.unop := rfl

/-- Connecting components are the original finite-category connecting maps. -/
@[simp] theorem kloostermanBocksteinConnectingSystem_app (d : ℕ) (n : ℕᵒᵖ) :
    (kloostermanBocksteinConnectingSystem p ell hne d).app n =
      kloostermanFiniteBocksteinConnecting p ell hne d n.unop := rfl

/-- The actual scalar and reduction transformations compose to zero. -/
theorem kloostermanBocksteinSystem_scalar_comp_reduction (d : ℕ) :
    kloostermanBocksteinScalarSystem p ell hne d ≫
      kloostermanBocksteinReductionSystem p ell hne d = 0 := by
  apply NatTrans.ext
  funext n
  exact kloostermanFiniteBockstein_scalar_comp_reduction p ell hne d n.unop

/-- The actual reduction and connecting transformations compose to zero. -/
theorem kloostermanBocksteinSystem_reduction_comp_connecting (d : ℕ) :
    kloostermanBocksteinReductionSystem p ell hne d ≫
      kloostermanBocksteinConnectingSystem p ell hne d = 0 := by
  apply NatTrans.ext
  funext n
  exact kloostermanFiniteBockstein_reduction_comp_connecting p ell hne d n.unop

/-- The actual connecting and next-degree scalar transformations compose to zero. -/
theorem kloostermanBocksteinSystem_connecting_comp_scalar (d : ℕ) :
    kloostermanBocksteinConnectingSystem p ell hne d ≫
      kloostermanBocksteinScalarSystem p ell hne (d + 1) = 0 := by
  apply NatTrans.ext
  funext n
  exact kloostermanFiniteBockstein_connecting_comp_scalar p ell hne d n.unop

/-- The first consecutive triple is exact in the actual functor category. -/
theorem kloostermanBocksteinSystem_exact_source (d : ℕ) :
    (ShortComplex.mk (kloostermanBocksteinScalarSystem p ell hne d)
      (kloostermanBocksteinReductionSystem p ell hne d)
      (kloostermanBocksteinSystem_scalar_comp_reduction p ell hne d)).Exact := by
  apply (functorShortComplex_exact_iff_eval _).mpr
  intro n
  exact kloostermanFiniteBockstein_exact_source p ell hne d n.unop

/-- The middle triple is exact at the original finite-category derived tower. -/
theorem kloostermanBocksteinSystem_exact_torsion (d : ℕ) :
    (ShortComplex.mk (kloostermanBocksteinReductionSystem p ell hne d)
      (kloostermanBocksteinConnectingSystem p ell hne d)
      (kloostermanBocksteinSystem_reduction_comp_connecting p ell hne d)).Exact := by
  apply (functorShortComplex_exact_iff_eval _).mpr
  intro n
  exact kloostermanFiniteBockstein_exact_torsion p ell hne d n.unop

/-- The third consecutive triple is exact at the next-degree power tower. -/
theorem kloostermanBocksteinSystem_exact_next (d : ℕ) :
    (ShortComplex.mk (kloostermanBocksteinConnectingSystem p ell hne d)
      (kloostermanBocksteinScalarSystem p ell hne (d + 1))
      (kloostermanBocksteinSystem_connecting_comp_scalar p ell hne d)).Exact := by
  apply (functorShortComplex_exact_iff_eval _).mpr
  intro n
  exact kloostermanFiniteBockstein_exact_next p ell hne d n.unop

#print axioms functorShortComplex_exact_iff_eval
#print axioms kloostermanFiniteBocksteinConnecting_naturality
#print axioms kloostermanBocksteinPowerTower
#print axioms kloostermanBocksteinPowerTower_obj
#print axioms kloostermanBocksteinPowerTower_map
#print axioms kloostermanBocksteinScalarSystem
#print axioms kloostermanBocksteinReductionSystem
#print axioms kloostermanBocksteinConnectingSystem
#print axioms kloostermanBocksteinScalarSystem_app
#print axioms kloostermanBocksteinReductionSystem_app
#print axioms kloostermanBocksteinConnectingSystem_app
#print axioms kloostermanBocksteinSystem_scalar_comp_reduction
#print axioms kloostermanBocksteinSystem_reduction_comp_connecting
#print axioms kloostermanBocksteinSystem_connecting_comp_scalar
#print axioms kloostermanBocksteinSystem_exact_source
#print axioms kloostermanBocksteinSystem_exact_torsion
#print axioms kloostermanBocksteinSystem_exact_next

end PrimeGap182.TypeIII
