import TypeIIIProjectiveTorusChart
import TypeIIIKloostermanPhaseFamily
import TypeIIIEtaleExtensionExact

/-!
# A compactification of the original Kloosterman phase family

The existing affine family Spec F_p[t,u,u⁻¹,v,v⁻¹] is identified with
the actual open chart D₊(XYZ) in P² over F_p[t].  Its original projection
to Spec F_p[t] factors through the proved proper projective-plane
projection.  For prime p the open immersion has dense image.
The homogeneous fraction (X²Y+XY²+tZ³)/(XYZ) on this chart is identified
with the unchanged original phase function u+v+t/(uv).

The same actual open immersion is packaged as a monomorphic étale
object.  It therefore defines the existing extension-by-zero functor
on module sheaves, with its adjunction, exactness and geometric stalk
formulas.  This is an underived construction; no compactly supported
cohomology or cohomological trace formula is asserted.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable (p : ℕ)

/-- The actual projective plane over the original affine parameter ring. -/
abbrev kloostermanCompactificationScheme : Scheme :=
  projectivePlaneModel (Polynomial (ZMod p))

/-- The actual proper projection to the original parameter line. -/
def kloostermanCompactificationProjection :
    kloostermanCompactificationScheme p ⟶ Spec (.of (Polynomial (ZMod p))) :=
  projectivePlaneToBase (Polynomial (ZMod p))

instance kloostermanCompactificationProjection_isProper :
    IsProper (kloostermanCompactificationProjection p) :=
  inferInstanceAs (IsProper (projectivePlaneToBase (Polynomial (ZMod p))))

/-- The original affine phase scheme is isomorphic to the literal projective chart. -/
def kloostermanPhaseChartIso :
    kloostermanPhaseScheme p ≅
      Spec (.of (ProjectivePlaneTorusChart (Polynomial (ZMod p)))) :=
  Scheme.Spec.mapIso (projectiveTorusChartEquiv (Polynomial (ZMod p))).toCommRingCatIso.op

@[simp] theorem kloostermanPhaseChartIso_hom :
    (kloostermanPhaseChartIso p).hom =
      Spec.map (CommRingCat.ofHom
        (projectiveTorusChartEquiv (Polynomial (ZMod p))).toRingHom) := rfl

/-- The actual open immersion of the original phase family into the proper model. -/
def kloostermanCompactificationOpenImmersion :
    kloostermanPhaseScheme p ⟶ kloostermanCompactificationScheme p :=
  (kloostermanPhaseChartIso p).hom ≫ projectivePlaneTorusChartι (Polynomial (ZMod p))

instance kloostermanCompactificationOpenImmersion_isOpenImmersion :
    IsOpenImmersion (kloostermanCompactificationOpenImmersion p) := by
  unfold kloostermanCompactificationOpenImmersion
  infer_instance

/-- Its image is exactly the actual projective basic open D₊(XYZ). -/
theorem kloostermanCompactificationOpenImmersion_opensRange :
    (kloostermanCompactificationOpenImmersion p).opensRange =
      Proj.basicOpen (projectivePlaneGrading (Polynomial (ZMod p)))
        (projectivePlaneXYZ (Polynomial (ZMod p))) := by
  exact (Scheme.Hom.opensRange_comp_of_isIso (kloostermanPhaseChartIso p).hom
    (projectivePlaneTorusChartι (Polynomial (ZMod p)))).trans
      (projectivePlaneTorusChartι_opensRange (Polynomial (ZMod p)))

/-- For prime p the original phase family is dense in its proper model. -/
theorem kloostermanCompactificationOpenImmersion_denseRange [Fact p.Prime] :
    DenseRange (kloostermanCompactificationOpenImmersion p) := by
  change Dense ((kloostermanCompactificationOpenImmersion p).opensRange :
    Set (kloostermanCompactificationScheme p))
  rw [kloostermanCompactificationOpenImmersion_opensRange]
  have h := projectivePlaneTorusChartι_denseRange (Polynomial (ZMod p))
  change Dense ((projectivePlaneTorusChartι (Polynomial (ZMod p))).opensRange :
    Set (projectivePlaneModel (Polynomial (ZMod p)))) at h
  simpa only [projectivePlaneTorusChartι_opensRange] using h

/-- This is a factorization of the unchanged original phase-family projection. -/
theorem kloostermanCompactificationOpenImmersion_toBase :
    kloostermanCompactificationOpenImmersion p ≫ kloostermanCompactificationProjection p =
      kloostermanPhaseProjection p := by
  rw [kloostermanCompactificationOpenImmersion, kloostermanCompactificationProjection,
    Category.assoc, projectivePlaneTorusChartι_toBase, kloostermanPhaseChartIso_hom,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, projectiveTorusChartEquiv_coefficient]
  rfl

/-- The actual open immersion as an object of the proper model's small étale site. -/
def kloostermanCompactificationEtaleObject :
    (kloostermanCompactificationScheme p).Etale :=
  Scheme.Etale.mk (kloostermanCompactificationOpenImmersion p)

@[simp] theorem kloostermanCompactificationEtaleObject_left :
    (kloostermanCompactificationEtaleObject p).left = kloostermanPhaseScheme p := rfl

@[simp] theorem kloostermanCompactificationEtaleObject_hom :
    (kloostermanCompactificationEtaleObject p).hom =
      kloostermanCompactificationOpenImmersion p := rfl

instance kloostermanCompactificationEtaleObject_mono :
    Mono (kloostermanCompactificationEtaleObject p).hom := by
  change Mono (kloostermanCompactificationOpenImmersion p)
  infer_instance

/-- The homogeneous fraction defining the original phase on the actual torus chart. -/
def kloostermanCompactificationChartPhase :
    ProjectivePlaneTorusChart (Polynomial (ZMod p)) :=
  projectiveTorusChartPhase (Polynomial (ZMod p)) Polynomial.X

/-- The actual chart equivalence identifies that fraction with the original phase function. -/
theorem kloostermanCompactificationChartPhase_eq_phaseFunction :
    projectiveTorusChartEquiv (Polynomial (ZMod p)) (kloostermanCompactificationChartPhase p) =
      kloostermanPhaseFunction p :=
  projectiveTorusChartEquiv_phase (Polynomial (ZMod p)) Polynomial.X

section ModuleSheaves

variable (E : Type) [Ring E]

/-- Actual restriction from the proper model to the original phase family. -/
def kloostermanPhaseRestriction :
    Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology (ModuleCat.{0} E) ⥤
      Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E) :=
  EtaleExtensionByZero.restriction (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E

/-- Actual extension by zero of module sheaves on the original phase family. -/
def kloostermanPhaseExtensionByZero :
    Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E) ⥤
      Sheaf (kloostermanCompactificationScheme p).smallEtaleTopology (ModuleCat.{0} E) :=
  EtaleExtensionByZero.functor (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E

/-- The constructed extension is left adjoint to the actual restriction. -/
def kloostermanPhaseExtensionByZeroAdjunction :
    kloostermanPhaseExtensionByZero p E ⊣ kloostermanPhaseRestriction p E :=
  EtaleExtensionByZero.adjunction (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E

instance kloostermanPhaseExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (kloostermanPhaseExtensionByZero p E) :=
  EtaleExtensionByZero.functor_preservesFiniteLimits (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E

instance kloostermanPhaseExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (kloostermanPhaseExtensionByZero p E) :=
  EtaleExtensionByZero.functor_preservesFiniteColimits (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E

instance kloostermanPhaseExtensionByZero_additive :
    (kloostermanPhaseExtensionByZero p E).Additive :=
  EtaleExtensionByZero.functor_additive (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E

/-- Actual short exact sequences remain short exact under the constructed extension. -/
theorem kloostermanPhaseExtensionByZero_map_shortExact
    (T : ShortComplex (Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)))
    (hT : T.ShortExact) : (T.map (kloostermanPhaseExtensionByZero p E)).ShortExact :=
  EtaleExtensionByZero.map_shortExact (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E T hT

/-- At a point of the original family, the extended stalk is its original stalk. -/
def kloostermanPhaseExtensionByZero_stalkIso (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (q : Spec (.of Ω) ⟶ kloostermanPhaseScheme p) :
    kloostermanPhaseExtensionByZero p E ⋙
        (Scheme.pointSmallEtale (q ≫ kloostermanCompactificationOpenImmersion p)).sheafFiber ≅
      (Scheme.pointSmallEtale q).sheafFiber :=
  EtaleExtensionByZero.stalkIso (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) Ω q E

/-- At every geometric point outside the actual phase-family image, the stalk is zero. -/
theorem kloostermanPhaseExtensionByZero_stalk_isZero (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (q : Spec (.of Ω) ⟶ kloostermanCompactificationScheme p)
    (hq : q default ∉ Set.range (kloostermanCompactificationOpenImmersion p))
    (F : Sheaf (kloostermanPhaseScheme p).smallEtaleTopology (ModuleCat.{0} E)) :
    IsZero ((Scheme.pointSmallEtale q).sheafFiber.obj
      ((kloostermanPhaseExtensionByZero p E).obj F)) :=
  EtaleExtensionByZero.stalk_isZero (kloostermanCompactificationScheme p)
    (kloostermanCompactificationEtaleObject p) E Ω q hq F

end ModuleSheaves

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.kloostermanCompactificationScheme
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationProjection
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationProjection_isProper
#print axioms PrimeGap182.TypeIII.kloostermanPhaseChartIso
#print axioms PrimeGap182.TypeIII.kloostermanPhaseChartIso_hom
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_isOpenImmersion
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_opensRange
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_denseRange
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationOpenImmersion_toBase
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationEtaleObject
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationEtaleObject_left
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationEtaleObject_hom
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationEtaleObject_mono
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationChartPhase
#print axioms PrimeGap182.TypeIII.kloostermanCompactificationChartPhase_eq_phaseFunction
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRestriction
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZeroAdjunction
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_preservesFiniteLimits
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_preservesFiniteColimits
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_additive
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_map_shortExact
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_stalkIso
#print axioms PrimeGap182.TypeIII.kloostermanPhaseExtensionByZero_stalk_isZero
