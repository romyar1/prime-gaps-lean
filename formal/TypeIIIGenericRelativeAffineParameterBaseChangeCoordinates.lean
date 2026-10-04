import TypeIIIFourierSourceOpenCartesianFromLaurentLocalization
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
The original parameter self-map extends to the full relative affine line by
its coefficient homomorphism, keeping the polynomial source coordinate.
The universal polynomial ring pushout proves the full relative Cartesian
square for EVERY ring homomorphism. The supplied original generic square
and source-coordinate identity force the extension to restrict to the exact
original g, and force f to fix the original PhaseField constants. No selected
map, field-presentation equality, sheaf base-change or MODEL law is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PrimeGap182.TypeIII.GenericRelativeAffineParameterBaseChangeCoordinates
open GenericRelativeAffineLineCoordinates GenericSourceSpecialization GenericCurvePullback
open PublishedPhaseApplication FourierSourceMaps RelativeAffineFourierKernelFromActualCoordinates

variable (R S : Type) [CommRing R] [CommRing S] (f : R →+* S)

/-- The universal polynomial base-change square in actual commutative rings. -/
theorem polynomialSquare_isPushout :
    IsPushout (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R))
      (CommRingCat.ofHom f) (CommRingCat.ofHom (MvPolynomial.map f))
      (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial (Fin 1) S)) := by
  have w : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R) ≫
      CommRingCat.ofHom (MvPolynomial.map f) =
    CommRingCat.ofHom f ≫ CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial (Fin 1) S) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact MvPolynomial.map_C f a
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (MvPolynomial.eval₂Hom s.inr.hom
      (fun i : Fin 1 => s.inl.hom (MvPolynomial.X i)))) ?_ ?_ ?_)
  · intro s
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change (MvPolynomial.eval₂Hom s.inr.hom (fun i : Fin 1 => s.inl.hom (MvPolynomial.X i)))
        (MvPolynomial.map f (MvPolynomial.C a)) = s.inl.hom (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      have h := congrArg (fun q => q.hom a) s.condition
      change s.inl.hom (MvPolynomial.C a) = s.inr.hom (f a) at h
      exact h.symm
    · intro i
      change (MvPolynomial.eval₂Hom s.inr.hom (fun i : Fin 1 => s.inl.hom (MvPolynomial.X i)))
        (MvPolynomial.map f (MvPolynomial.X i)) = s.inl.hom (MvPolynomial.X i)
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact MvPolynomial.eval₂Hom_C _ _ a
  · intro s q hleft hright
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change q.hom (MvPolynomial.C a) =
        (MvPolynomial.eval₂Hom s.inr.hom (fun i : Fin 1 => s.inl.hom (MvPolynomial.X i))) (MvPolynomial.C a)
      rw [MvPolynomial.eval₂Hom_C]
      have h := congrArg (fun r => r.hom a) hright
      exact h
    · intro i
      change q.hom (MvPolynomial.X i) =
        (MvPolynomial.eval₂Hom s.inr.hom (fun i : Fin 1 => s.inl.hom (MvPolynomial.X i))) (MvPolynomial.X i)
      rw [MvPolynomial.eval₂Hom_X']
      have h := congrArg (fun r => r.hom (MvPolynomial.X i)) hleft
      change q.hom (MvPolynomial.map f (MvPolynomial.X i)) = s.inl.hom (MvPolynomial.X i) at h
      simpa only [MvPolynomial.map_X] using h

/-- Spec gives the actual polynomial Cartesian square, without field hypotheses. -/
theorem polynomialSquare_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map f)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial (Fin 1) S)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R)))
      (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomialSquare_isPushout R S f)

variable (K : Type) [Field K]

/-- Exact coefficient homomorphism of an arbitrary original parameter map. -/
def parameterHom (f : parameterScheme K ⟶ parameterScheme K) : ParameterRing K →+* ParameterRing K :=
  (Spec.preimage f).hom

/-- Keep source X polynomial while applying f to every original parameter coefficient. -/
def relativeMap (f : parameterScheme K ⟶ parameterScheme K) : relativeAffineScheme K ⟶ relativeAffineScheme K :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (parameterHom K f)))

/-- Every original parameter map has the genuine full relative Cartesian square. -/
theorem relativeMap_isPullback (f : parameterScheme K ⟶ parameterScheme K) :
    IsPullback (relativeMap K f) (relativeProjection K) (relativeProjection K) f := by
  have h := polynomialSquare_isPullback (ParameterRing K) (ParameterRing K) (parameterHom K f)
  change IsPullback (relativeMap K f) (relativeProjection K) (relativeProjection K) (Spec.map (Spec.preimage f)) at h
  simpa only [Spec.map_preimage] using h

/-- Actual source A1 is the affine-line product over the original PhaseField. -/
theorem sourceProjection_isPullback :
    IsPullback (sourceMorphism K) (relativeProjection K)
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : PhaseField K →+* MvPolynomial (Fin 1) (PhaseField K))))
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PhaseField K →+* ParameterRing K))) := by
  have h := polynomialSquare_isPullback (PhaseField K) (ParameterRing K)
    (LaurentPolynomial.C : PhaseField K →+* ParameterRing K)
  have e : sourceHom K = MvPolynomial.map (LaurentPolynomial.C : PhaseField K →+* ParameterRing K) := by
    apply MvPolynomial.ringHom_ext <;> intro a
    · simp only [sourceHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.map_C]
    · have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
      simp only [sourceHom, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, ha]
  simpa only [sourceMorphism, relativeProjection, e] using h

variable (f : parameterScheme K ⟶ parameterScheme K)
  (g : genericScheme K ⟶ genericScheme K)
  (square : IsPullback g (genericProjection K) (genericProjection K) f)
  (coordinate : g ≫ projectionMorphism K = projectionMorphism K)

/-- Exact original π-square equation on ALL parameter coefficients. -/
theorem genericHom_comp_C (square : IsPullback g (genericProjection K) (genericProjection K) f) :
    (Spec.preimage g).hom.comp LaurentPolynomial.C =
      LaurentPolynomial.C.comp (parameterHom K f) := by
  have h := congrArg (fun a => (Spec.preimage a).hom) square.w
  simp only [Spec.preimage_comp, genericProjection, Spec.preimage_map] at h
  exact h

/-- The labelled source-coordinate guard fixes the invertible Laurent X. -/
theorem genericHom_variable (coordinate : g ≫ projectionMorphism K = projectionMorphism K) :
    (Spec.preimage g).hom (curveUnit K : GenericRing K) = (curveUnit K : GenericRing K) := by
  have h := congrArg (fun a => (Spec.preimage a).hom) coordinate
  simp only [Spec.preimage_comp, projectionMorphism, Spec.preimage_map] at h
  change (Spec.preimage g).hom.comp (projectionHom K).toRingHom = (projectionHom K).toRingHom at h
  have hx := congrArg (fun q => q (LaurentPolynomial.T 1)) h
  change (Spec.preimage g).hom
    (LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K) (LaurentPolynomial.T 1)) =
    LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K) (LaurentPolynomial.T 1) at hx
  simpa only [LaurentPolynomial.eval₂_T, zpow_one] using hx

/-- f fixes PhaseField; this is derived from the original coordinate guard. -/
theorem parameterHom_phase (square : IsPullback g (genericProjection K) (genericProjection K) f) (coordinate : g ≫ projectionMorphism K = projectionMorphism K) (a : PhaseField K) :
    parameterHom K f (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  have h := congrArg (fun x => (Spec.preimage x).hom) coordinate
  simp only [Spec.preimage_comp, projectionMorphism, Spec.preimage_map] at h
  change (Spec.preimage g).hom.comp (projectionHom K).toRingHom = (projectionHom K).toRingHom at h
  have hc := congrArg (fun q => q (LaurentPolynomial.C a)) h
  change (Spec.preimage g).hom
    (LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K) (LaurentPolynomial.C a)) =
    LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K) (LaurentPolynomial.C a) at hc
  rw [LaurentPolynomial.eval₂_C] at hc
  have hs := congrArg (fun q => q (LaurentPolynomial.C a)) (genericHom_comp_C K f g square)
  change (Spec.preimage g).hom (LaurentPolynomial.C (LaurentPolynomial.C a)) =
    LaurentPolynomial.C (parameterHom K f (LaurentPolynomial.C a)) at hs
  change (Spec.preimage g).hom (LaurentPolynomial.C (LaurentPolynomial.C a)) =
    LaurentPolynomial.C (LaurentPolynomial.C a) at hc
  have eq := hs.symm.trans hc
  have coeff := congrArg (fun q : GenericRing K => q.coeff 0) eq
  simpa only [LaurentPolynomial.C_apply, ite_true] using coeff

/-- The exact original g is the restriction of the computed full relative map. -/
theorem relativeMap_open (square : IsPullback g (genericProjection K) (genericProjection K) f) (coordinate : g ≫ projectionMorphism K = projectionMorphism K) :
    g ≫ relativeOpenMorphism K = relativeOpenMorphism K ≫ relativeMap K f := by
  dsimp only [relativeOpenMorphism, relativeMap]
  rw [← Spec.map_preimage g, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change (Spec.preimage g).hom (relativeOpenHom K (MvPolynomial.C a)) =
      relativeOpenHom K (MvPolynomial.map (parameterHom K f) (MvPolynomial.C a))
    simp only [MvPolynomial.map_C, relativeOpenHom_C]
    exact DFunLike.congr_fun (genericHom_comp_C K f g square) a
  · intro i
    change (Spec.preimage g).hom (relativeOpenHom K (MvPolynomial.X i)) =
      relativeOpenHom K (MvPolynomial.map (parameterHom K f) (MvPolynomial.X i))
    simp only [MvPolynomial.map_X, relativeOpenHom_X]
    exact genericHom_variable K g coordinate

/-- The computed full relative map preserves the actual full source line. -/
theorem relativeMap_source (square : IsPullback g (genericProjection K) (genericProjection K) f) (coordinate : g ≫ projectionMorphism K = projectionMorphism K) : relativeMap K f ≫ sourceMorphism K = sourceMorphism K := by
  dsimp only [relativeMap, sourceMorphism]
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.map (parameterHom K f) (sourceHom K (MvPolynomial.C a)) = sourceHom K (MvPolynomial.C a)
    simp only [sourceHom, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, MvPolynomial.map_C]
    exact congrArg MvPolynomial.C (parameterHom_phase K f g square coordinate a)
  · intro i
    change MvPolynomial.map (parameterHom K f) (sourceHom K (MvPolynomial.X i)) = sourceHom K (MvPolynomial.X i)
    simp only [sourceHom, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X]

end PrimeGap182.TypeIII.GenericRelativeAffineParameterBaseChangeCoordinates
