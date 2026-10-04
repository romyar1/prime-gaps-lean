import TypeIIIFourierStalkFromSources

/-!
# Pull back the original three-factor curve input

The target KloostermanInputData is constructed from inverse images of the
original three sources. General fiber-property preservation supplies its
properties. Monoidality and pullback compatibility with duals identify
its tensor recipe with inverse image of the original complete input.
-/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.PulledCurveInput

open PublishedPhysicalConstruction

universe u v w z a b
variable {Input : Type u} [Category.{a} Input] {Point : Type w}
  {Input' : Type v} [Category.{b} Input'] {Point' : Type z}
  (D : CurveData Input Point) (D' : CurveData Input' Point') (F : Input ⥤ Input')

/-- General inverse-image laws on curve inputs, before choosing the
three sources. The dual comparison is required only for lisse inputs. -/
structure PullbackProperties where
  lisse : ∀ A, D.Lisse A → D'.Lisse (F.obj A)
  rank : ∀ A, D.Lisse A → D'.rank (F.obj A) = D.rank A
  pure : ∀ A t, D.Pure A t → D'.Pure (F.obj A) t
  tame : ∀ A, D.TameZero A → D'.TameZero (F.obj A)
  breaks : ∀ A s, D.BreaksLE A s → D'.BreaksLE (F.obj A) s
  slope : ∀ A s, D.Isoclinic A s → D'.Isoclinic (F.obj A) s
  dual : ∀ A, D.Lisse A → (F.obj (D.dual A) ≅ D'.dual (F.obj A))

variable (R : PullbackProperties D D' F)

def pulledInput (A : KloostermanInputData D) : KloostermanInputData D' where
  first := F.obj A.first
  second := F.obj A.second
  additive := F.obj A.additive
  first_lisse := R.lisse A.first A.first_lisse
  second_lisse := R.lisse A.second A.second_lisse
  additive_lisse := R.lisse A.additive A.additive_lisse
  first_rank := (R.rank A.first A.first_lisse).trans A.first_rank
  second_rank := (R.rank A.second A.second_lisse).trans A.second_rank
  additive_rank := (R.rank A.additive A.additive_lisse).trans A.additive_rank
  first_pure := R.pure A.first 0 A.first_pure
  second_pure := R.pure A.second 0 A.second_pure
  additive_pure := R.pure A.additive 0 A.additive_pure
  first_tame := R.tame A.first A.first_tame
  second_tame := R.tame A.second A.second_tame
  additive_tame := R.tame A.additive A.additive_tame
  first_breaks := R.breaks A.first (1 / 3) A.first_breaks
  second_breaks := R.breaks A.second (1 / 3) A.second_breaks
  additive_slope := R.slope A.additive 1 A.additive_slope

variable [MonoidalCategory Input] [MonoidalCategory Input'] [F.Monoidal]
  (tensorSource : ∀ A B, D.tensor A B ≅ A ⊗ B)
  (tensorTarget : ∀ A B, D'.tensor A B ≅ A ⊗ B)

def pullTensorIso (A B : Input) :
    F.obj (D.tensor A B) ≅ D'.tensor (F.obj A) (F.obj B) :=
  F.mapIso (tensorSource A B) ≪≫ (Functor.Monoidal.μIso F A B).symm ≪≫
    (tensorTarget (F.obj A) (F.obj B)).symm

def targetTensorIso {A B A' B' : Input'} (a : A ≅ A') (b : B ≅ B') :
    D'.tensor A B ≅ D'.tensor A' B' :=
  tensorTarget A B ≪≫ tensorIso a b ≪≫ (tensorTarget A' B').symm

/-- The full original tensor recipe, not only its three factors, is
identified with the constructed target input. -/
def pulledInputIso (A : KloostermanInputData D) :
    F.obj A.input ≅ (pulledInput D D' F R A).input :=
  pullTensorIso D D' F tensorSource tensorTarget (D.tensor A.first (D.dual A.second)) A.additive ≪≫
    targetTensorIso D' tensorTarget
      (pullTensorIso D D' F tensorSource tensorTarget A.first (D.dual A.second) ≪≫
        targetTensorIso D' tensorTarget (Iso.refl (F.obj A.first)) (R.dual A.second A.second_lisse))
      (Iso.refl (F.obj A.additive))

end PrimeGap182.TypeIII.PulledCurveInput

#print axioms PrimeGap182.TypeIII.PulledCurveInput.pulledInput
#print axioms PrimeGap182.TypeIII.PulledCurveInput.pullTensorIso
#print axioms PrimeGap182.TypeIII.PulledCurveInput.targetTensorIso
#print axioms PrimeGap182.TypeIII.PulledCurveInput.pulledInputIso
