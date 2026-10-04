import TypeIIIGloballyLisseLineRamificationFromKatz
import TypeIIISourceLocalTensorDualFromUniformProfiles

/-!
# Scalar local propagation through the actual parameter fibers

The ring and SAME-U composition identities are proved from the literal
source specialization and scalar maps. Scalar origin action is transported
along an actual group automorphism, not identified on a fixed inertia group.
Geometric constant-field extension has its own explicit local realization
comparison. The ALL-globally-lisse profile comparisons and filtered-group
meaning remain general theorem/model data, not selected source clauses.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PrimeGap182.TypeIII.ScalarLocalPropagationFromFilteredTraits
open ExactInverseImagesToDerived PrimitiveRamificationFromGeneralKatzTheory
open UniformSourceLocalObservablesFromParameterFibers

variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- Literal Laurent coefficient extension, retaining the variable. -/
def baseGmHom : ArithmeticSourceMaps.FiberRing K →ₐ[K] ArithmeticSourceMaps.FiberRing E where
  toRingHom := LaurentPolynomial.eval₂
    (LaurentPolynomial.C.comp (algebraMap K E)) (PhysicalTorusLaurent.variableUnit E)
  commutes' c := by
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C ((algebraMap K K) c)) = _
    rw [LaurentPolynomial.eval₂_C]
    simp only [Algebra.algebraMap_self_apply]
    rfl

def baseGmMorphism : ArithmeticSourceMaps.fiberScheme E ⟶ ArithmeticSourceMaps.fiberScheme K :=
  Spec.map (CommRingCat.ofHom (baseGmHom K E).toRingHom)

theorem baseGmHom_comp_localInput :
    (baseGmHom K E).comp (ArithmeticSourceMaps.localInputHom K K) =
      ArithmeticSourceMaps.localInputHom K E := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, ArithmeticSourceMaps.localInputHom, aeval_X]
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem baseGmMorphism_comp_localInput :
    baseGmMorphism K E ≫ ArithmeticSourceMaps.localInputMorphism K K =
      ArithmeticSourceMaps.localInputMorphism K E := by
  dsimp only [baseGmMorphism, ArithmeticSourceMaps.localInputMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (baseGmHom_comp_localInput K E))

/-- The underlying scalar ring homomorphism is independent of its base algebra. -/
theorem scalarMorphism_self (a : Eˣ) :
    ArithmeticSourceMaps.scalarMorphism K E a = ArithmeticSourceMaps.scalarMorphism E E a := rfl

universe mu
variable (C : Scheme.{0} → Type) [∀ X, Category.{mu} (C X)] [∀ X, Abelian (C X)]
  (U : OrdinarySystem (fun X : Scheme.{0} => X) C)
  (L : ∀ X : Scheme, ObjectProperty (C X))
  (M : LocalRealization C)

/-- SAME-U composition along the proved literal coefficient-extension square. -/
def localInputBaseIso (A : C (StartingSourceMaps.affineLine K)) :
    (U.pull (ArithmeticSourceMaps.localInputMorphism K E)).obj A ≅
      (U.pull (baseGmMorphism K E)).obj
        ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A) :=
  eqToIso (congrArg (fun f => (U.pull f).obj A) (baseGmMorphism_comp_localInput K E).symm) ≪≫
    ((U.composition (baseGmMorphism K E) (ArithmeticSourceMaps.localInputMorphism K K)).app A).symm

/-- SAME-U scalar source specialization; no sheaf comparison is supplied. -/
def specializedScalarIso (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (lambda xi : Eˣ) (A : C (StartingSourceMaps.affineLine K)) :
    (U.pull (ArithmeticSourceMaps.specializationMorphism K E lambda xi)).obj
      ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) ≅
      (U.pull (ArithmeticSourceMaps.scalarMorphism E E
        (ScalarSourceSpecializationCoordinates.coefficientValue K E c lambda xi))).obj
          ((U.pull (ArithmeticSourceMaps.localInputMorphism K E)).obj A) :=
  (U.composition (ArithmeticSourceMaps.specializationMorphism K E lambda xi)
    (CanonicalCurveInput.scalarMorphism K c)).app A ≪≫
  eqToIso (congrArg (fun f => (U.pull f).obj A)
    (ScalarSourceSpecializationCoordinates.specialization_scalarMorphism K E c lambda xi)) ≪≫
  ((U.composition (ArithmeticSourceMaps.scalarMorphism K E
    (ScalarSourceSpecializationCoordinates.coefficientValue K E c lambda xi))
    (ArithmeticSourceMaps.localInputMorphism K E)).app A).symm ≪≫
  eqToIso (congrArg (fun f => (U.pull f).obj
    ((U.pull (ArithmeticSourceMaps.localInputMorphism K E)).obj A))
    (scalarMorphism_self K E _))

/-- Pulling an action along a wild-preserving group map preserves wild triviality. -/
theorem wildTrivial_restrict {H J : Type} [Group H] [Group J]
    (P : Subgroup H) (Q : Subgroup J) (f : H →* J)
    (hf : ∀ g : P, f g.val ∈ Q) (V : FDRep (PadicAlgCl 2) J) (hV : wildTrivial Q V) :
    wildTrivial P ((Action.res (FGModuleCat (PadicAlgCl 2)) f).obj V) := by
  intro g
  exact hV ⟨f g.val, hf g⟩

variable
  (lissePull : ∀ {X Y : Scheme} (f : X ⟶ Y) (A : C Y), L Y A → L X ((U.pull f).obj A))
  (scalarOriginAutomorphism : ∀ (F : Type) [Field F], (2 : F) ≠ 0 →
    Fˣ → M.originGroup F ≃* M.originGroup F)
  (scalarOriginWild : ∀ (F : Type) [Field F] (h2 : (2 : F) ≠ 0) (a : Fˣ)
    (g : M.wildOrigin F), scalarOriginAutomorphism F h2 a g.val ∈ M.wildOrigin F)
  (scalarOriginComparison : ∀ (F : Type) [Field F] (h2 : (2 : F) ≠ 0) (a : Fˣ),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙
      U.pull (ArithmeticSourceMaps.scalarMorphism F F a) ⋙ M.origin F ≅
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
      Action.res (FGModuleCat (PadicAlgCl 2)) (scalarOriginAutomorphism F h2 a).toMonoidHom)
  (scalarProfile : ∀ (F : Type) [Field F] (_h2 : (2 : F) ≠ 0) (a : Fˣ)
    (A : C (ArithmeticSourceMaps.fiberScheme F)), L (ArithmeticSourceMaps.fiberScheme F) A →
      (M.profile F ((U.pull (ArithmeticSourceMaps.scalarMorphism F F a)).obj A)).multiplicity =
        (M.profile F A).multiplicity)
  (baseOriginHom : ∀ (F B : Type) [Field F] [Field B] [Algebra F B],
    (2 : F) ≠ 0 → (2 : B) ≠ 0 → M.originGroup B →* M.originGroup F)
  (baseOriginWild : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0) (g : M.wildOrigin B),
    baseOriginHom F B hF hB g.val ∈ M.wildOrigin F)
  (baseOriginComparison : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (hF : (2 : F) ≠ 0) (hB : (2 : B) ≠ 0),
    (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ U.pull (baseGmMorphism F B) ⋙ M.origin B ≅
      (L (ArithmeticSourceMaps.fiberScheme F)).ι ⋙ M.origin F ⋙
        Action.res (FGModuleCat (PadicAlgCl 2)) (baseOriginHom F B hF hB))
  (baseProfile : ∀ (F B : Type) [Field F] [Field B] [Algebra F B]
    (_hF : (2 : F) ≠ 0) (_hB : (2 : B) ≠ 0)
    (A : C (ArithmeticSourceMaps.fiberScheme F)), L (ArithmeticSourceMaps.fiberScheme F) A →
      (M.profile B ((U.pull (baseGmMorphism F B)).obj A)).multiplicity =
        (M.profile F A).multiplicity)

include scalarOriginWild scalarOriginComparison in
/-- General scalar action transport preserves tame origin on globally lisse Gm. -/
theorem scalar_tame (hE : (2 : E) ≠ 0) (a : Eˣ)
    (A : C (ArithmeticSourceMaps.fiberScheme E)) (hL : L (ArithmeticSourceMaps.fiberScheme E) A)
    (hA : wildTrivial (M.wildOrigin E) ((M.origin E).obj A)) :
    wildTrivial (M.wildOrigin E) ((M.origin E).obj
      ((U.pull (ArithmeticSourceMaps.scalarMorphism E E a)).obj A)) :=
  wildTrivial_iso _ ((scalarOriginComparison E hE a).app ⟨A, hL⟩).symm
    (wildTrivial_restrict _ _ (scalarOriginAutomorphism E hE a).toMonoidHom
      (scalarOriginWild E hE a) _ hA)

include baseOriginWild baseOriginComparison in
/-- Geometric constant-field local realization transport preserves tame origin. -/
theorem base_tame (hK : (2 : K) ≠ 0) (hE : (2 : E) ≠ 0)
    (A : C (ArithmeticSourceMaps.fiberScheme K)) (hL : L (ArithmeticSourceMaps.fiberScheme K) A)
    (hA : wildTrivial (M.wildOrigin K) ((M.origin K).obj A)) :
    wildTrivial (M.wildOrigin E) ((M.origin E).obj ((U.pull (baseGmMorphism K E)).obj A)) :=
  wildTrivial_iso _ ((baseOriginComparison K E hK hE).app ⟨A, hL⟩).symm
    (wildTrivial_restrict _ _ (baseOriginHom K E hK hE)
      (baseOriginWild K E hK hE) _ hA)

section ScalarSource
variable [∀ X, (L X).IsClosedUnderIsomorphisms] (hK : (2 : K) ≠ 0)

include lissePull scalarOriginWild scalarOriginComparison baseOriginWild baseOriginComparison hK in
/-- Exact original guarded scalar tame clause, uniform on EVERY parameter fiber. -/
theorem scalar_source_tame (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K))
    (hA : GloballyLisseLineRamificationFromKatz.tameZero C U L M K A) :
    sourceTameZero K C U L M ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) := by
  refine ⟨SourceGlobalLissityFromKatzPullbacks.scalar_lisse K C U L lissePull c A hA.1, ?_⟩
  intro t
  let F := t.coefficientField
  let b := ScalarSourceSpecializationCoordinates.coefficientValue K F c t.lambda t.xi
  have hF : (2 : F) ≠ 0 := SourceLocalTensorDualFromUniformProfiles.parameter_two_ne_zero K hK t
  let B := (U.pull (ArithmeticSourceMaps.localInputMorphism K F)).obj A
  have hLB : L (ArithmeticSourceMaps.fiberScheme F) B :=
    (L _).prop_of_iso (localInputBaseIso K F C U A).symm
      (lissePull _ _ hA.1)
  have hTB : wildTrivial (M.wildOrigin F) ((M.origin F).obj B) :=
    wildTrivial_iso _ ((M.origin F).mapIso (localInputBaseIso K F C U A)).symm
      (base_tame K F C U L M baseOriginHom baseOriginWild baseOriginComparison hK hF _ hA.1 hA.2)
  exact wildTrivial_iso _ ((M.origin F).mapIso (specializedScalarIso K F C U c t.lambda t.xi A)).symm
    (scalar_tame F C U L M scalarOriginAutomorphism scalarOriginWild scalarOriginComparison hF b B hLB hTB)

include lissePull scalarProfile baseProfile hK in
/-- Exact profile identity after original scalar source pullback and specialization. -/
theorem scalar_source_profile (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K))
    (hA : SourceGlobalLissityFromKatzPullbacks.lineLisseOnUnits K C U L A) (t : ParameterPoint K) :
    (sourceInfinityProfile K C U M ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) t).multiplicity =
      (M.profile K ((U.pull (ArithmeticSourceMaps.localInputMorphism K K)).obj A)).multiplicity := by
  let F := t.coefficientField
  let b := ScalarSourceSpecializationCoordinates.coefficientValue K F c t.lambda t.xi
  have hF : (2 : F) ≠ 0 := SourceLocalTensorDualFromUniformProfiles.parameter_two_ne_zero K hK t
  let B := (U.pull (ArithmeticSourceMaps.localInputMorphism K F)).obj A
  have hLB : L (ArithmeticSourceMaps.fiberScheme F) B :=
    (L _).prop_of_iso (localInputBaseIso K F C U A).symm (lissePull _ _ hA)
  exact (M.profile_localIso F _ _ ((M.infinity F).mapIso
    (specializedScalarIso K F C U c t.lambda t.xi A))).trans
    ((scalarProfile F hF b B hLB).trans
      ((M.profile_localIso F _ _ ((M.infinity F).mapIso (localInputBaseIso K F C U A))).trans
        (baseProfile K F hK hF _ hA)))

include lissePull scalarProfile baseProfile hK in
/-- Exact original guarded scalar bounded-break clause on EVERY parameter fiber. -/
theorem scalar_source_breaks (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K)) (s : ℚ)
    (hA : GloballyLisseLineRamificationFromKatz.breaksLE C U L M K A s) :
    sourceBreaksLE K C U L M ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) s := by
  refine ⟨SourceGlobalLissityFromKatzPullbacks.scalar_lisse K C U L lissePull c A hA.1, ?_⟩
  intro t r hr
  rw [scalar_source_profile K C U L M lissePull scalarProfile baseProfile hK c A hA.1 t] at hr
  exact hA.2 r hr

include lissePull scalarProfile baseProfile hK in
/-- Exact original guarded scalar isoclinic clause on EVERY parameter fiber. -/
theorem scalar_source_isoclinic (c : (PhysicalTorusMorphism.TorusRing K)ˣ)
    (A : C (StartingSourceMaps.affineLine K)) (s : ℚ)
    (hA : GloballyLisseLineRamificationFromKatz.isoclinic C U L M K A s) :
    sourceIsoclinic K C U L M ((U.pull (CanonicalCurveInput.scalarMorphism K c)).obj A) s := by
  refine ⟨SourceGlobalLissityFromKatzPullbacks.scalar_lisse K C U L lissePull c A hA.1, ?_⟩
  intro t r hr
  rw [scalar_source_profile K C U L M lissePull scalarProfile baseProfile hK c A hA.1 t] at hr
  exact hA.2 r hr
end ScalarSource

end PrimeGap182.TypeIII.ScalarLocalPropagationFromFilteredTraits
