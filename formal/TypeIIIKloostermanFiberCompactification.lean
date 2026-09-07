import TypeIIIEtaleCohomology
import TypeIIIEtaleOpenExtensionBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The actual compactification fiber of the unchanged phase family

The proper model and its phase open are pulled back along an actual
field-valued parameter.  Pasting the original cartesian squares and
using the proved factorization of the original phase projection
identifies the pulled-back open with the fiber of that same projection.
Both projections of this identification are recorded.

The cohomology functor at the end is global cohomology on this proper
fiber of extension by zero from its actual phase open.  Thus it uses a
compactification over the specified field.  No comparison with the
stalk of the relative derived image, independence of compactification,
adic comparison, or trace formula is assumed or proved here.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) {K : Type} [Field K]
  (s : Spec (.of K) ⟶ Spec (.of (Polynomial (ZMod p))))

/-- The literal fiber of the existing proper compactification. -/
abbrev kloostermanCompactificationFiber : Scheme :=
  pullback (kloostermanCompactificationProjection p) s

/-- Its actual structure morphism to the specified field. -/
def kloostermanCompactificationFiberProjection :
    kloostermanCompactificationFiber p s ⟶ Spec (.of K) :=
  pullback.snd (kloostermanCompactificationProjection p) s

/-- Properness holds over the specified field by actual scheme base change. -/
instance kloostermanCompactificationFiberProjection_isProper :
    IsProper (kloostermanCompactificationFiberProjection p s) := by
  dsimp only [kloostermanCompactificationFiberProjection]
  infer_instance

/-- The actual pulled-back phase open inside that fiber, with its literal nested pullback. -/
abbrev kloostermanPhaseFiberOpen : Scheme :=
  pullback (pullback.fst (kloostermanCompactificationProjection p) s)
    (kloostermanCompactificationOpenImmersion p)

/-- The original phase open pulled back into the actual compactification fiber. -/
def kloostermanPhaseFiberOpenImmersion :
    kloostermanPhaseFiberOpen p s ⟶ kloostermanCompactificationFiber p s :=
  pullback.fst (pullback.fst (kloostermanCompactificationProjection p) s)
    (kloostermanCompactificationOpenImmersion p)

/-- This literal pulled-back map is an open immersion. -/
instance kloostermanPhaseFiberOpenImmersion_isOpenImmersion :
    IsOpenImmersion (kloostermanPhaseFiberOpenImmersion p s) := by
  dsimp only [kloostermanPhaseFiberOpenImmersion]
  infer_instance

/-- The actual map from the pulled-back phase open to the original phase family. -/
def kloostermanPhaseFiberToPhase :
    kloostermanPhaseFiberOpen p s ⟶ kloostermanPhaseScheme p :=
  pullback.snd (pullback.fst (kloostermanCompactificationProjection p) s)
    (kloostermanCompactificationOpenImmersion p)

/-- The nested open is the fiber of the unchanged original phase projection. -/
def kloostermanPhaseFiberOpenIso :
    kloostermanPhaseFiberOpen p s ≅ pullback (kloostermanPhaseProjection p) s :=
  pullbackSymmetry (pullback.fst (kloostermanCompactificationProjection p) s)
      (kloostermanCompactificationOpenImmersion p) ≪≫
    pullbackRightPullbackFstIso (kloostermanCompactificationProjection p) s
      (kloostermanCompactificationOpenImmersion p) ≪≫
    pullback.congrHom (kloostermanCompactificationOpenImmersion_toBase p) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identification preserves the map to the original phase family. -/
@[reassoc]
theorem kloostermanPhaseFiberOpenIso_hom_fst :
    (kloostermanPhaseFiberOpenIso p s).hom ≫ pullback.fst (kloostermanPhaseProjection p) s =
      kloostermanPhaseFiberToPhase p s := by
  simp [kloostermanPhaseFiberOpenIso, kloostermanPhaseFiberToPhase,
    pullback.congrHom_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The identification also preserves the actual projection to the specified field. -/
@[reassoc]
theorem kloostermanPhaseFiberOpenIso_hom_snd :
    (kloostermanPhaseFiberOpenIso p s).hom ≫ pullback.snd (kloostermanPhaseProjection p) s =
      kloostermanPhaseFiberOpenImmersion p s ≫
        kloostermanCompactificationFiberProjection p s := by
  simp [kloostermanPhaseFiberOpenIso, kloostermanPhaseFiberOpenImmersion,
    kloostermanCompactificationFiberProjection, pullback.congrHom_hom, Category.assoc]

variable (E : Type) [Ring E]

/-- Original coefficients pulled to the phase fiber and extended by zero into its proper model. -/
def kloostermanFiberPhaseExtension :
    Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E) ⥤
      Sheaf (kloostermanCompactificationFiber p s).smallEtaleTopology (ModuleCat.{0} E) :=
  EtaleInverseImage.functor (kloostermanPhaseFiberToPhase p s) E ⋙
    EtaleExtensionByZero.functor (kloostermanCompactificationFiber p s)
      (Scheme.Etale.mk (kloostermanPhaseFiberOpenImmersion p s)) E

/-- This uses the same actual extension as the proved arbitrary-pullback comparison. -/
def kloostermanFiberPhaseExtensionIso :
    kloostermanPhaseExtensionByZero p E ⋙
        EtaleInverseImage.functor (pullback.fst (kloostermanCompactificationProjection p) s) E ≅
      kloostermanFiberPhaseExtension p s E :=
  kloostermanPhaseExtensionByZero_parameterBaseChangeIso p E s

/-- Global cohomology of the actual extended sheaf on the actual proper fiber over K. -/
def kloostermanFiberCompactCohomology (n : ℕ) :
    Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E) ⥤ ModuleCat.{0} E :=
  kloostermanFiberPhaseExtension p s E ⋙
    EtaleCohomology.functor (kloostermanCompactificationFiber p s) E n

/-- The value is literally the derived global sections on the specified proper fiber. -/
theorem kloostermanFiberCompactCohomology_obj (n : ℕ)
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    (kloostermanFiberCompactCohomology p s E n).obj F =
      ((EtaleCohomology.sections (kloostermanCompactificationFiber p s) E).rightDerived n).obj
        ((kloostermanFiberPhaseExtension p s E).obj F) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- These actual cohomology functors are additive. -/
instance kloostermanFiberCompactCohomology_additive (n : ℕ) :
    (kloostermanFiberCompactCohomology p s E n).Additive := by
  let : Mono (Scheme.Etale.mk (kloostermanPhaseFiberOpenImmersion p s)).hom :=
    inferInstanceAs (Mono (kloostermanPhaseFiberOpenImmersion p s))
  let : (EtaleInverseImage.functor (kloostermanPhaseFiberToPhase p s) E).Additive :=
    EtaleInverseImage.functor_additive _ _
  let : (EtaleExtensionByZero.functor (kloostermanCompactificationFiber p s)
      (Scheme.Etale.mk (kloostermanPhaseFiberOpenImmersion p s)) E).Additive :=
    EtaleExtensionByZero.functor_additive _ _ _
  let : (EtaleCohomology.functor (kloostermanCompactificationFiber p s) E n).Additive :=
    EtaleCohomology.functor_additive _ _ _
  dsimp only [kloostermanFiberCompactCohomology, kloostermanFiberPhaseExtension]
  infer_instance

#print axioms kloostermanCompactificationFiber
#print axioms kloostermanCompactificationFiberProjection
#print axioms kloostermanCompactificationFiberProjection_isProper
#print axioms kloostermanPhaseFiberOpen
#print axioms kloostermanPhaseFiberOpenImmersion
#print axioms kloostermanPhaseFiberOpenImmersion_isOpenImmersion
#print axioms kloostermanPhaseFiberToPhase
#print axioms kloostermanPhaseFiberOpenIso
#print axioms kloostermanPhaseFiberOpenIso_hom_fst
#print axioms kloostermanPhaseFiberOpenIso_hom_snd
#print axioms kloostermanFiberPhaseExtension
#print axioms kloostermanFiberPhaseExtensionIso
#print axioms kloostermanFiberCompactCohomology
#print axioms kloostermanFiberCompactCohomology_obj
#print axioms kloostermanFiberCompactCohomology_additive

end PrimeGap182.TypeIII
