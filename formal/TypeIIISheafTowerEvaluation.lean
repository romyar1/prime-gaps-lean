import TypeIIIEtaleTowerDirectImage
import TypeIIIDerivedBaseChangeIso
import TypeIIIDerivedBaseChangeTransformation
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Evaluation of actual étale sheaf towers and derived direct images

Evaluation at a level of the original tower category is exact. Its
original left adjoint is a coproduct indexed by arrows of the tower
index category. These arrow sets are subsingleton, so the coproducts
are finite and preserve monomorphisms. Thus evaluation preserves
injective objects without any additional injectivity assumption.

The original reflexive evaluation square for pointwise q_* therefore
gives the original derived comparison isomorphism. Its resolution,
augmentation, degree-zero, and index-naturality formulas retain the
existing comparison maps and chosen injective resolutions.

This is a comparison at each level of the tower. It makes no claim
that an ordinary inverse limit is exact or commutes with cohomology,
and asserts no proper base change or adic comparison.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII.EtaleSheafTowerEvaluation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

section Evaluation

variable (S : Scheme.{u}) (E : Type u) [Ring E] (n : ℕ)

/-- The original evaluation functor at the specified tower level. -/
def functor : EtaleSheafTower.Tower S E ⥤
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  (evaluation ℕᵒᵖ (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj (op n)

/-- Evaluation retains the literal object of the original tower. -/
@[simp] theorem functor_obj (T : EtaleSheafTower.Tower S E) :
    (functor S E n).obj T = T.obj (op n) := rfl

/-- Evaluation retains the literal component of the original tower morphism. -/
@[simp] theorem functor_map {T T' : EtaleSheafTower.Tower S E} (a : T ⟶ T') :
    (functor S E n).map a = a.app (op n) := rfl

/-- Arrow sets in the tower index are subsingleton, so their coproducts exist by finite colimits. -/
instance homCoproducts :
    ∀ k l : ℕᵒᵖ, HasCoproductsOfShape (k ⟶ l)
      (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) := by
  intro k l
  exact hasColimitsOfShape_discrete (C := Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (k ⟶ l)

/-- The original coproduct left adjoint to evaluation. -/
def leftAdjoint : Sheaf S.smallEtaleTopology (ModuleCat.{u} E) ⥤
    EtaleSheafTower.Tower S E :=
  evaluationLeftAdjoint (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (op n)

/-- This is Mathlib's original evaluation adjunction. -/
def adjunction : leftAdjoint S E n ⊣ functor S E n :=
  evaluationAdjunctionRight (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (op n)

/-- At a level, the left adjoint map is the original coproduct map. -/
theorem leftAdjoint_map_app {A B : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)}
    (f : A ⟶ B) (k : ℕᵒᵖ) :
    ((leftAdjoint S E n).map f).app k =
      CategoryTheory.Limits.Sigma.map (fun _ : op n ⟶ k => f) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro a
  simp [leftAdjoint, evaluationLeftAdjoint]

/-- The coproducts in the actual left adjoint are finite, hence preserve monomorphisms. -/
instance leftAdjoint_preservesMonomorphisms :
    (leftAdjoint S E n).PreservesMonomorphisms where
  preserves {A B} f hf := by
    let : HasFiniteBiproducts (Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :=
      Abelian.hasFiniteBiproducts
    have : ∀ k : ℕᵒᵖ, Mono (((leftAdjoint S E n).map f).app k) := by
      intro k
      rw [leftAdjoint_map_app]
      exact CategoryTheory.Limits.Sigma.map_mono (fun _ : op n ⟶ k => f)
    exact NatTrans.mono_of_mono_app ((leftAdjoint S E n).map f)

/-- Evaluation is additive on the actual module-sheaf tower category. -/
instance functor_additive : (functor S E n).Additive :=
  inferInstanceAs (((evaluation ℕᵒᵖ
    (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj (op n)).Additive)

/-- Finite limits of the actual tower category are computed level by level. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor S E n) where
  preservesFiniteLimits J _ _ := by
    change PreservesLimitsOfShape J
      ((evaluation ℕᵒᵖ (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj (op n))
    infer_instance

/-- Finite colimits of the actual tower category are computed level by level. -/
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor S E n) where
  preservesFiniteColimits J _ _ := by
    change PreservesColimitsOfShape J
      ((evaluation ℕᵒᵖ (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).obj (op n))
    infer_instance

/-- Exact evaluation preserves the original homology objects. -/
instance functor_preservesHomology : (functor S E n).PreservesHomology := inferInstance

/-- The original evaluation functor takes short exact sequences to short exact sequences. -/
theorem map_shortExact (T : ShortComplex (EtaleSheafTower.Tower S E))
    (hT : T.ShortExact) : (T.map (functor S E n)).ShortExact :=
  hT.map_of_exact (functor S E n)

/-- The proved monomorphism preservation of its actual left adjoint gives injective preservation. -/
instance functor_preservesInjectiveObjects : (functor S E n).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (adjunction S E n)

variable {n}

/-- A tower arrow gives the original natural transformation between evaluations. -/
def transition {k l : ℕᵒᵖ} (a : k ⟶ l) :
    functor S E k.unop ⟶ functor S E l.unop :=
  (evaluation ℕᵒᵖ (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))).map a

/-- Its component is the original tower transition. -/
@[simp] theorem transition_app {k l : ℕᵒᵖ} (a : k ⟶ l)
    (T : EtaleSheafTower.Tower S E) :
    (transition S E a).app T = T.map a := rfl

end Evaluation

section Comparison

variable {X S : Scheme.{u}} (q : X ⟶ S) (E : Type u) [Ring E] (n : ℕ)

/-- Evaluation and pointwise direct image commute by the original reflexive square. -/
def evaluationSquareIso :
    EtaleTowerDirectImage.functor q E ⋙ functor S E n ≅
      functor X E n ⋙ EtaleDirectImage.functor q E :=
  Iso.refl _

/-- Every ordinary component is the identity of the original direct-image sheaf. -/
@[simp] theorem evaluationSquareIso_hom_app (T : EtaleSheafTower.Tower X E) :
    (evaluationSquareIso q E n).hom.app T =
      𝟙 ((EtaleDirectImage.functor q E).obj (T.obj (op n))) := rfl

/-- The actual resolution comparison is invertible because evaluation preserves injectives. -/
def evaluationResolutionIso :
    (EtaleTowerDirectImage.functor q E).rightDerivedToHomotopyCategory ⋙
        (functor S E n).mapHomotopyCategory (ComplexShape.up ℕ) ≅
      functor X E n ⋙ (EtaleDirectImage.functor q E).rightDerivedToHomotopyCategory :=
  derivedBaseChangeResolutionIso (EtaleTowerDirectImage.functor q E)
    (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
    (evaluationSquareIso q E n).hom

/-- The forward map is the original resolution comparison, not a replacement isomorphism. -/
@[simp] theorem evaluationResolutionIso_hom :
    (evaluationResolutionIso q E n).hom =
      derivedBaseChangeResolutionMap (EtaleTowerDirectImage.functor q E)
        (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
        (evaluationSquareIso q E n).hom := rfl

/-- Its component is the quotient of the original comparison on the chosen injective resolution. -/
theorem evaluationResolutionIso_hom_app (T : EtaleSheafTower.Tower X E) :
    (evaluationResolutionIso q E n).hom.app T =
      (HomotopyCategory.quotient (Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
        (ComplexShape.up ℕ)).map
          (derivedBaseChangeChainMap (EtaleTowerDirectImage.functor q E)
            (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
            (evaluationSquareIso q E n).hom (injectiveResolution T)) :=
  derivedBaseChangeResolutionMap_app (EtaleTowerDirectImage.functor q E)
    (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
    (evaluationSquareIso q E n).hom T

/-- The actual chain comparison extends the original ordinary evaluation component. -/
theorem evaluationChainMap_augmentation {T : EtaleSheafTower.Tower X E}
    (I : InjectiveResolution T) :
    (functor S E n).map ((EtaleTowerDirectImage.functor q E).map (I.ι.f 0)) ≫
        (derivedBaseChangeChainMap (EtaleTowerDirectImage.functor q E)
          (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
          (evaluationSquareIso q E n).hom I).f 0 =
      (evaluationSquareIso q E n).hom.app T ≫
        (EtaleDirectImage.functor q E).map
          ((injectiveResolution ((functor X E n).obj T)).ι.f 0) :=
  derivedBaseChangeChainMap_augmentation (EtaleTowerDirectImage.functor q E)
    (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
    (evaluationSquareIso q E n).hom I

/-- The original derived direct image of towers agrees at each level with the original derived q_*. -/
def evaluationBaseChangeIso (d : ℕ) :
    (EtaleTowerDirectImage.functor q E).rightDerived d ⋙ functor S E n ≅
      functor X E n ⋙ (EtaleDirectImage.functor q E).rightDerived d :=
  derivedBaseChangeIso (EtaleTowerDirectImage.functor q E)
    (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
    (evaluationSquareIso q E n).hom d

/-- The forward morphism is literally the original derived comparison map. -/
@[simp] theorem evaluationBaseChangeIso_hom (d : ℕ) :
    (evaluationBaseChangeIso q E n d).hom =
      derivedBaseChangeMap (EtaleTowerDirectImage.functor q E)
        (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
        (evaluationSquareIso q E n).hom d := rfl

/-- The original degree-zero comparison respects both canonical maps to the zeroth derived functor. -/
theorem evaluationBaseChangeIso_zero :
    Functor.whiskerRight (EtaleTowerDirectImage.functor q E).toRightDerivedZero
        (functor S E n) ≫ (evaluationBaseChangeIso q E n 0).hom =
      (evaluationSquareIso q E n).hom ≫
        Functor.whiskerLeft (functor X E n) (EtaleDirectImage.functor q E).toRightDerivedZero :=
  derivedBaseChangeMap_zero (EtaleTowerDirectImage.functor q E)
    (EtaleDirectImage.functor q E) (functor X E n) (functor S E n)
    (evaluationSquareIso q E n).hom

/-- The degree-zero isomorphism is the ordinary reflexive square through the original zero isomorphisms. -/
theorem evaluationBaseChangeIso_zero_eq :
    (evaluationBaseChangeIso q E n 0).hom =
      Functor.whiskerRight (EtaleTowerDirectImage.functor q E).rightDerivedZeroIsoSelf.hom
          (functor S E n) ≫
        (evaluationSquareIso q E n).hom ≫
          Functor.whiskerLeft (functor X E n)
            (EtaleDirectImage.functor q E).rightDerivedZeroIsoSelf.inv := by
  let Z := Functor.isoWhiskerRight
    (EtaleTowerDirectImage.functor q E).rightDerivedZeroIsoSelf (functor S E n)
  rw [← cancel_epi Z.inv]
  change Z.inv ≫ (evaluationBaseChangeIso q E n 0).hom = Z.inv ≫ Z.hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  exact evaluationBaseChangeIso_zero q E n

variable {n}

/-- The original evaluation squares commute with the actual arrows of the tower index. -/
theorem evaluationSquareIso_transition {k l : ℕᵒᵖ} (a : k ⟶ l) :
    (evaluationSquareIso q E k.unop).hom ≫
        Functor.whiskerRight (transition X E a) (EtaleDirectImage.functor q E) =
      Functor.whiskerLeft (EtaleTowerDirectImage.functor q E) (transition S E a) ≫
        (evaluationSquareIso q E l.unop).hom := by
  ext T
  simp [evaluationSquareIso, transition, functor, EtaleTowerDirectImage.functor]

/-- The original derived comparison is natural in the level of the tower. -/
theorem evaluationBaseChangeIso_transition (d : ℕ) {k l : ℕᵒᵖ} (a : k ⟶ l) :
    (evaluationBaseChangeIso q E k.unop d).hom ≫
        Functor.whiskerRight (transition X E a) ((EtaleDirectImage.functor q E).rightDerived d) =
      Functor.whiskerLeft ((EtaleTowerDirectImage.functor q E).rightDerived d)
          (transition S E a) ≫
        (evaluationBaseChangeIso q E l.unop d).hom :=
  derivedBaseChangeMap_transformation (EtaleTowerDirectImage.functor q E)
    (EtaleDirectImage.functor q E) (functor X E k.unop) (functor X E l.unop)
    (functor S E k.unop) (functor S E l.unop) (transition X E a) (transition S E a)
    (evaluationSquareIso q E k.unop).hom (evaluationSquareIso q E l.unop).hom
    (evaluationSquareIso_transition q E a) d

/-- At a tower object this is compatibility with its literal original transition maps. -/
theorem evaluationBaseChangeIso_index_naturality (d : ℕ) {k l : ℕᵒᵖ} (a : k ⟶ l)
    (T : EtaleSheafTower.Tower X E) :
    (((EtaleTowerDirectImage.functor q E).rightDerived d).obj T).map a ≫
        (evaluationBaseChangeIso q E l.unop d).hom.app T =
      (evaluationBaseChangeIso q E k.unop d).hom.app T ≫
        ((EtaleDirectImage.functor q E).rightDerived d).map (T.map a) := by
  exact (NatTrans.congr_app (evaluationBaseChangeIso_transition q E d a) T).symm

end Comparison

#print axioms functor
#print axioms functor_obj
#print axioms functor_map
#print axioms homCoproducts
#print axioms leftAdjoint
#print axioms adjunction
#print axioms leftAdjoint_map_app
#print axioms leftAdjoint_preservesMonomorphisms
#print axioms functor_additive
#print axioms functor_preservesFiniteLimits
#print axioms functor_preservesFiniteColimits
#print axioms functor_preservesHomology
#print axioms map_shortExact
#print axioms functor_preservesInjectiveObjects
#print axioms transition
#print axioms transition_app
#print axioms evaluationSquareIso
#print axioms evaluationSquareIso_hom_app
#print axioms evaluationResolutionIso
#print axioms evaluationResolutionIso_hom
#print axioms evaluationResolutionIso_hom_app
#print axioms evaluationChainMap_augmentation
#print axioms evaluationBaseChangeIso
#print axioms evaluationBaseChangeIso_hom
#print axioms evaluationBaseChangeIso_zero
#print axioms evaluationBaseChangeIso_zero_eq
#print axioms evaluationSquareIso_transition
#print axioms evaluationBaseChangeIso_transition
#print axioms evaluationBaseChangeIso_index_naturality

end PrimeGap182.TypeIII.EtaleSheafTowerEvaluation
