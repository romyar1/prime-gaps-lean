import TypeIIIArithmeticSourceTransport
import TypeIIIRegularUnipotentRepresentation

/-!
# Original arithmetic source models from primitive scalar-source data

Only the one-variable scalar pullbacks of the two primitive sources are
modeled here. The three original family identifications and their source
normalizations are constructed using the proved arithmetic pullback maps.
The primitive source models and general specialization laws remain
explicit inputs; this module does not instantiate a sheaf theory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace PrimeGap182.TypeIII.ArithmeticPrimitiveSources

open StartingSourceMaps ArithmeticSourceMaps ArithmeticSourceTransport
open PublishedPhaseApplication RegularUnipotentRepresentation

universe u v w a b c d
variable (K E : Type) [Field K] [Field E] [Algebra K E]
  {Line : Type u} [Category.{a} Line] {Input : Type v} [Category.{b} Input]
  {Local : Type w} [Category.{c} Local] {G : Type d} [Group G]
  {original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input}
  (P : Pullbacks (Local := Local) K E original) (J : Local ⥤ FDRep ℂ G)
  (LF : LocalFrobenius J) (kl as : Line) (tame : G →* Multiplicative ℂ)

/-- The scalar pullback of one fixed primitive source on the local curve. -/
def scalarSource (A : Line) (a : Eˣ) : Local :=
  (P.localEnd (scalarMorphism K E a)).obj ((P.specialized (localInputMorphism K E)).obj A)

/-- Explicit primitive source data, for every nonzero scalar. This has
no field about a finished correlation, family boundary, or original
family-source identification. These data still require a realization. -/
structure ScalarSourceModels where
  klZero : ∀ a : Eˣ, Representation.Equiv (J.obj (scalarSource K E P kl a)).ρ (tameRepresentation tame)
  asZero : ∀ a : Eˣ, Representation.Equiv (J.obj (scalarSource K E P as a)).ρ (Representation.trivial ℂ G ℂ)
  scalar : ℂ
  scalar_ne_zero : scalar ≠ 0
  klLine : ∀ a : Eˣ,
    LF.action (scalarSource K E P kl a) ((klZero a).toLinearEquiv.symm (Pi.single 0 1)) =
      scalar • (klZero a).toLinearEquiv.symm (Pi.single 0 1)
  asAction : ∀ (a : Eˣ) x,
    asZero a (LF.action (scalarSource K E P as a) x) = asZero a x

variable {K E P J LF kl as tame}
  (S : ScalarSourceModels K E P J LF kl as tame)
  (zero : Input → FDRep ℂ G) (Fr : ∀ A, (zero A).V ≃ₗ[ℂ] (zero A).V)
  (lambda xi : Eˣ)
  (SC : SpecializationComparison J (P.along (specializationMorphism K E lambda xi)) zero Fr LF)

/-- The actual first source, via the unit scalar pullback. -/
def ScalarSourceModels.firstZero :
    Representation.Equiv (zero ((original (inputMorphism K 0)).obj kl)).ρ (tameRepresentation tame) :=
  sourceModelEquiv J zero Fr LF K E P lambda xi SC (tameRepresentation tame) kl 0 (S.klZero 1)

/-- The actual second source, via scalar multiplication by lambda. -/
def ScalarSourceModels.secondZero :
    Representation.Equiv (zero ((original (inputMorphism K 1)).obj kl)).ρ (tameRepresentation tame) :=
  sourceModelEquiv J zero Fr LF K E P lambda xi SC (tameRepresentation tame) kl 1 (S.klZero lambda)

/-- The actual additive source, via scalar multiplication by xi. -/
def ScalarSourceModels.additiveZero :
    Representation.Equiv (zero ((original (inputMorphism K 2)).obj as)).ρ (Representation.trivial ℂ G ℂ) :=
  sourceModelEquiv J zero Fr LF K E P lambda xi SC (Representation.trivial ℂ G ℂ) as 2 (S.asZero xi)

/-- Source normalization on the original first source is transported
through the same constructed arithmetic comparison. -/
theorem ScalarSourceModels.firstInvariantLine :
    Fr ((original (inputMorphism K 0)).obj kl)
      ((S.firstZero zero Fr lambda xi SC).toLinearEquiv.symm (Pi.single 0 1)) =
    S.scalar • (S.firstZero zero Fr lambda xi SC).toLinearEquiv.symm (Pi.single 0 1) :=
  sourceModel_eigenvector J zero Fr LF K E P lambda xi SC (tameRepresentation tame)
    kl 0 (S.klZero 1) (Pi.single 0 1) S.scalar (S.klLine 1)

/-- The same primitive normalization gives the SAME scalar on the
original second source; no equality of full Frobenius matrices is used. -/
theorem ScalarSourceModels.secondInvariantLine :
    Fr ((original (inputMorphism K 1)).obj kl)
      ((S.secondZero zero Fr lambda xi SC).toLinearEquiv.symm (Pi.single 0 1)) =
    S.scalar • (S.secondZero zero Fr lambda xi SC).toLinearEquiv.symm (Pi.single 0 1) :=
  sourceModel_eigenvector J zero Fr LF K E P lambda xi SC (tameRepresentation tame)
    kl 1 (S.klZero lambda) (Pi.single 0 1) S.scalar (S.klLine lambda)

/-- The original additive-origin action follows from the primitive AS
normalization through the constructed source comparison. -/
theorem ScalarSourceModels.additiveNatural (x : (zero ((original (inputMorphism K 2)).obj as)).V) :
    S.additiveZero zero Fr lambda xi SC (Fr ((original (inputMorphism K 2)).obj as) x) =
      S.additiveZero zero Fr lambda xi SC x :=
  sourceModel_frobenius_trivial J zero Fr LF K E P lambda xi SC (Representation.trivial ℂ G ℂ)
    as 2 (S.asZero xi) (S.asAction xi) x

end PrimeGap182.TypeIII.ArithmeticPrimitiveSources

#print axioms PrimeGap182.TypeIII.ArithmeticPrimitiveSources.ScalarSourceModels.firstZero
#print axioms PrimeGap182.TypeIII.ArithmeticPrimitiveSources.ScalarSourceModels.secondZero
#print axioms PrimeGap182.TypeIII.ArithmeticPrimitiveSources.ScalarSourceModels.additiveZero
#print axioms PrimeGap182.TypeIII.ArithmeticPrimitiveSources.ScalarSourceModels.firstInvariantLine
#print axioms PrimeGap182.TypeIII.ArithmeticPrimitiveSources.ScalarSourceModels.secondInvariantLine
#print axioms PrimeGap182.TypeIII.ArithmeticPrimitiveSources.ScalarSourceModels.additiveNatural
