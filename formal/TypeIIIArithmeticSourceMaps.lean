import TypeIIIFourierSourceMaps

/-!
# Arithmetic specialization of the three original source maps

Over an arbitrary coefficient extension E/K, specialize lambda and xi to
units while retaining the curve variable in E[x,x^-1]. The three original
maps then factor as the scalar maps 1, lambda and xi followed by the same
inclusion into A1_K. These are scheme identities, not identities tested
only on the finitely many E-valued points. General pullback composition
then gives the three source isomorphisms on that actual arithmetic fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial

namespace PrimeGap182.TypeIII.ArithmeticSourceMaps

open StartingSourceMaps

variable (K E : Type) [Field K] [Field E] [Algebra K E]

abbrev FiberRing := LaurentPolynomial E
abbrev fiberScheme : Scheme := Spec (.of (FiberRing E))

def constantUnit (a : Eˣ) : (FiberRing E)ˣ :=
  Units.map (LaurentPolynomial.C : E →+* FiberRing E).toMonoidHom a

def specializationHom (lambda xi : Eˣ) : SourceRing K →ₐ[K] FiberRing E :=
  evaluation (PhysicalTorusLaurent.variableUnit E) (constantUnit E lambda) (constantUnit E xi)

def localInputHom : MvPolynomial (Fin 1) K →ₐ[K] FiberRing E :=
  aeval (fun _ => (PhysicalTorusLaurent.variableUnit E : FiberRing E))

def scalarHom (a : Eˣ) : FiberRing E →ₐ[K] FiberRing E where
  toRingHom := LaurentPolynomial.eval₂ LaurentPolynomial.C
    (constantUnit E a * PhysicalTorusLaurent.variableUnit E)
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C (algebraMap K E c)) = _
    rw [LaurentPolynomial.eval₂_C]
    rfl

/-- Factor the exact coordinate map, retaining the Laurent variable. -/
theorem specialization_inputHom (lambda xi : Eˣ) (i : Fin 3) :
    (specializationHom K E lambda xi).comp (inputHom K i) =
      (scalarHom K E (![1, lambda, xi] i)).comp (localInputHom K E) := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  change evaluation (K := K) (PhysicalTorusLaurent.variableUnit E)
    (constantUnit E lambda) (constantUnit E xi) (inputHom K i (X 0)) =
      scalarHom K E (![1, lambda, xi] i) (localInputHom K E (X 0))
  rw [inputHom_evaluation]
  simp only [localInputHom, aeval_X]
  change ![(PhysicalTorusLaurent.variableUnit E : FiberRing E),
    (constantUnit E lambda : FiberRing E) * PhysicalTorusLaurent.variableUnit E,
    (constantUnit E xi : FiberRing E) * PhysicalTorusLaurent.variableUnit E] i =
    LaurentPolynomial.eval₂ (LaurentPolynomial.C : E →+* FiberRing E)
      (constantUnit E (![1, lambda, xi] i) * PhysicalTorusLaurent.variableUnit E)
      (LaurentPolynomial.T 1)
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  fin_cases i <;> simp [constantUnit]

def specializationMorphism (lambda xi : Eˣ) : fiberScheme E ⟶ sourceScheme K :=
  Spec.map (CommRingCat.ofHom (specializationHom K E lambda xi).toRingHom)

def localInputMorphism : fiberScheme E ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (localInputHom K E).toRingHom)

def scalarMorphism (a : Eˣ) : fiberScheme E ⟶ fiberScheme E :=
  Spec.map (CommRingCat.ofHom (scalarHom K E a).toRingHom)

/-- The arithmetic source factorization is an equality of schemes. -/
theorem specialization_inputMorphism (lambda xi : Eˣ) (i : Fin 3) :
    specializationMorphism K E lambda xi ≫ inputMorphism K i =
      scalarMorphism K E (![1, lambda, xi] i) ≫ localInputMorphism K E := by
  dsimp only [specializationMorphism, inputMorphism, scalarMorphism, localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (specialization_inputHom K E lambda xi i))

universe u v w a b c
variable {Line : Type u} [Category.{a} Line]
  {Input : Type v} [Category.{b} Input] {Local : Type w} [Category.{c} Local]

/-- General pullback composition on the same schemes. The original
inverse-image functor is a parameter, so the arithmetic and geometric
routes can share it literally rather than assume a family identification. -/
structure Pullbacks (original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input) where
  specialized : (fiberScheme E ⟶ affineLine K) → Line ⥤ Local
  along : (fiberScheme E ⟶ sourceScheme K) → Input ⥤ Local
  localEnd : (fiberScheme E ⟶ fiberScheme E) → Local ⥤ Local
  composition : ∀ g f, original f ⋙ along g ≅ specialized (g ≫ f)
  scalarComposition : ∀ g f, specialized f ⋙ localEnd g ≅ specialized (g ≫ f)

variable {original : (sourceScheme K ⟶ affineLine K) → Line ⥤ Input}
  (P : Pullbacks (Local := Local) K E original)

/-- All three original source pullbacks become scalar pullbacks of the
same primitive source. No source-specific isomorphism is an input. -/
def sourcePullbackIso (lambda xi : Eˣ) (i : Fin 3) :
    original (inputMorphism K i) ⋙ P.along (specializationMorphism K E lambda xi) ≅
      P.specialized (localInputMorphism K E) ⋙ P.localEnd (scalarMorphism K E (![1, lambda, xi] i)) :=
  P.composition (specializationMorphism K E lambda xi) (inputMorphism K i) ≪≫
    eqToIso (congrArg P.specialized (specialization_inputMorphism K E lambda xi i)) ≪≫
      (P.scalarComposition (scalarMorphism K E (![1, lambda, xi] i)) (localInputMorphism K E)).symm

end PrimeGap182.TypeIII.ArithmeticSourceMaps

#print axioms PrimeGap182.TypeIII.ArithmeticSourceMaps.specialization_inputHom
#print axioms PrimeGap182.TypeIII.ArithmeticSourceMaps.specialization_inputMorphism
#print axioms PrimeGap182.TypeIII.ArithmeticSourceMaps.sourcePullbackIso
