import TypeIIIFourierSourceMaps

/-!
# The Cartesian frequency substitution xi = T^2 / a

The source and frequency coordinate are kept separate. The curve map fixes
x, the base map sends xi to T^2/a, and the universal Fourier kernel xi*x
pulls back to the existing additiveMorphism. The pushout is verified for
arbitrary commutative target rings, not only geometric points.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.FourierNormalizationMaps

open PublishedPhaseApplication PhysicalTorusLaurent SourceCurveBaseChange
open GenericSourceSpecialization GenericCurvePullback FourierSourceMaps

universe u
variable (K : Type u) [Field K]

def frequencyHom (s : (PhaseField K)ˣ) : ParameterRing K →+* ParameterRing K :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C
    (variableUnit (PhaseField K) ^ 2 /
      Units.map (LaurentPolynomial.C : PhaseField K →+* ParameterRing K) s)

theorem frequencyHom_C (s : (PhaseField K)ˣ) (c : PhaseField K) :
    frequencyHom K s (LaurentPolynomial.C c) = LaurentPolynomial.C c :=
  LaurentPolynomial.eval₂_C _ _ _

section LaurentBaseChange
variable {A : Type u} [CommRing A] (f : A →+* A)

def curveHom : LaurentPolynomial A →+* LaurentPolynomial A :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : A →+* LaurentPolynomial A).comp f)
    (variableUnit A)

theorem curveHom_C (a : A) : curveHom f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) :=
  LaurentPolynomial.eval₂_C _ _ _

theorem curveHom_variable : Units.map (curveHom f).toMonoidHom (variableUnit A) = variableUnit A := by
  apply Units.ext
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem curveSquare_isPushout :
    IsPushout (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A))
      (CommRingCat.ofHom f) (CommRingCat.ofHom (curveHom f))
      (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)) := by
  have comm : (curveHom f).comp LaurentPolynomial.C = LaurentPolynomial.C.comp f := by
    apply RingHom.ext
    intro a
    exact curveHom_C f a
  have coeff {R : Type u} [CommRing R] (h : LaurentPolynomial A →+* R) (k : A →+* R) :
      (LaurentPolynomial.eval₂ k (Units.map h.toMonoidHom (variableUnit A))).comp LaurentPolynomial.C = k := by
    apply RingHom.ext
    intro a
    exact LaurentPolynomial.eval₂_C _ _ _
  have variable_eq {R : Type u} [CommRing R] (h : LaurentPolynomial A →+* R) (k : A →+* R) :
      Units.map (LaurentPolynomial.eval₂ k (Units.map h.toMonoidHom (variableUnit A))) (variableUnit A) =
        Units.map h.toMonoidHom (variableUnit A) := by
    apply Units.ext
    change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk
    (congrArg CommRingCat.ofHom comm)
    (fun s => CommRingCat.ofHom
      (LaurentPolynomial.eval₂ s.inr.hom (Units.map s.inl.hom.toMonoidHom (variableUnit A)))) ?_ ?_ ?_)
  · intro s
    apply CommRingCat.hom_ext
    apply laurent_ringHom_ext
    · change ((LaurentPolynomial.eval₂ s.inr.hom
        (Units.map s.inl.hom.toMonoidHom (variableUnit A))).comp (curveHom f)).comp
        LaurentPolynomial.C = s.inl.hom.comp LaurentPolynomial.C
      rw [RingHom.comp_assoc, comm, ← RingHom.comp_assoc, coeff]
      exact (congrArg CommRingCat.Hom.hom s.condition).symm
    · change Units.map (LaurentPolynomial.eval₂ s.inr.hom
        (Units.map s.inl.hom.toMonoidHom (variableUnit A))).toMonoidHom
        (Units.map (curveHom f).toMonoidHom (variableUnit A)) = _
      rw [curveHom_variable]
      exact variable_eq _ _
  · intro s
    apply CommRingCat.hom_ext
    exact coeff _ _
  · intro s q hf hg
    apply CommRingCat.hom_ext
    apply laurent_ringHom_ext
    · exact (congrArg CommRingCat.Hom.hom hg).trans (coeff _ _).symm
    · have h := congrArg (fun t : CommRingCat.of (LaurentPolynomial A) ⟶ s.pt =>
        Units.map t.hom.toMonoidHom (variableUnit A)) hf
      change Units.map q.hom.toMonoidHom (Units.map (curveHom f).toMonoidHom (variableUnit A)) = _ at h
      rw [curveHom_variable] at h
      exact h.trans (variable_eq _ _).symm

end LaurentBaseChange

def frequencyMorphism (s : (PhaseField K)ˣ) : parameterScheme K ⟶ parameterScheme K :=
  Spec.map (CommRingCat.ofHom (frequencyHom K s))

def curveMorphism (s : (PhaseField K)ˣ) : genericScheme K ⟶ genericScheme K :=
  Spec.map (CommRingCat.ofHom (curveHom (frequencyHom K s)))

theorem normalizationSquare_isPullback (s : (PhaseField K)ˣ) :
    IsPullback (curveMorphism K s) (genericProjection K)
      (genericProjection K) (frequencyMorphism K s) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (curveSquare_isPushout (frequencyHom K s))

theorem curve_projectionHom (s : (PhaseField K)ˣ) :
    (curveHom (frequencyHom K s)).comp (projectionHom K).toRingHom =
      (projectionHom K).toRingHom := by
  apply laurent_ringHom_ext
  · apply RingHom.ext
    intro c
    change curveHom (frequencyHom K s)
      (LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.C c)) = _
    rw [LaurentPolynomial.eval₂_C]
    change curveHom (frequencyHom K s) (LaurentPolynomial.C (LaurentPolynomial.C c)) = _
    rw [curveHom_C, frequencyHom_C]
    change LaurentPolynomial.C (LaurentPolynomial.C c) =
      LaurentPolynomial.eval₂ (algebraMap (PhaseField K) (GenericRing K)) (curveUnit K)
        (LaurentPolynomial.C c)
    rw [LaurentPolynomial.eval₂_C]
    rfl
  · change Units.map (curveHom (frequencyHom K s)).toMonoidHom
      (Units.map (projectionHom K).toRingHom.toMonoidHom (variableUnit (PhaseField K))) = _
    have hx : Units.map (projectionHom K).toRingHom.toMonoidHom (variableUnit (PhaseField K)) =
        variableUnit (ParameterRing K) := by
      apply Units.ext
      change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
      rw [LaurentPolynomial.eval₂_T, zpow_one]
      rfl
    rw [hx]
    exact curveHom_variable _

/-- The whole local x-projection is fixed, retaining its zero and infinity. -/
theorem curve_projection (s : (PhaseField K)ˣ) :
    curveMorphism K s ≫ projectionMorphism K = projectionMorphism K := by
  dsimp only [curveMorphism, projectionMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (curve_projectionHom K s)

def universalKernelHom : MvPolynomial (Fin 1) K →ₐ[K] GenericRing K :=
  MvPolynomial.aeval (fun _ => (parameterUnit K : GenericRing K) * (curveUnit K : GenericRing K))

def universalKernelMorphism : genericScheme K ⟶ StartingSourceMaps.affineLine K :=
  Spec.map (CommRingCat.ofHom (universalKernelHom K).toRingHom)

theorem curve_kernelHom (s : (PhaseField K)ˣ) :
    (curveHom (frequencyHom K s)).comp (universalKernelHom K).toRingHom =
      (additiveHom K s).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change curveHom (frequencyHom K s)
      ((universalKernelHom K) (MvPolynomial.C c)) = _
    rw [show MvPolynomial.C c = algebraMap K (MvPolynomial (Fin 1) K) c from rfl,
      AlgHom.commutes]
    change curveHom (frequencyHom K s)
      (LaurentPolynomial.C (LaurentPolynomial.C (algebraMap K (PhaseField K) c))) = _
    rw [curveHom_C, frequencyHom_C]
    exact (AlgHom.commutes (additiveHom K s) c).symm
  · intro i
    change curveHom (frequencyHom K s) ((universalKernelHom K) (MvPolynomial.X i)) = _
    change curveHom (frequencyHom K s) ((universalKernelHom K) (MvPolynomial.X i)) =
      (additiveHom K s) (MvPolynomial.X i)
    simp only [universalKernelHom, additiveHom, MvPolynomial.aeval_X, map_mul]
    have hx := congrArg Units.val (curveHom_variable (frequencyHom K s))
    have ht : Units.map (frequencyHom K s).toMonoidHom (variableUnit (PhaseField K)) =
        variableUnit (PhaseField K) ^ 2 /
          Units.map (LaurentPolynomial.C : PhaseField K →+* ParameterRing K).toMonoidHom s := by
      apply Units.ext
      change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
      rw [LaurentPolynomial.eval₂_T, zpow_one]
      rfl
    have hc : (curveHom (frequencyHom K s)).comp
        (LaurentPolynomial.C : ParameterRing K →+* GenericRing K) =
        LaurentPolynomial.C.comp (frequencyHom K s) := by
      apply RingHom.ext
      intro a
      exact curveHom_C _ a
    have hp : Units.map (curveHom (frequencyHom K s)).toMonoidHom (parameterUnit K) =
        parameterUnit K ^ 2 / constantUnit K s := by
      change Units.map ((curveHom (frequencyHom K s)).comp
        (LaurentPolynomial.C : ParameterRing K →+* GenericRing K)).toMonoidHom
        (variableUnit (PhaseField K)) = _
      rw [hc]
      change Units.map (LaurentPolynomial.C : ParameterRing K →+* GenericRing K).toMonoidHom
        (Units.map (frequencyHom K s).toMonoidHom (variableUnit (PhaseField K))) = _
      rw [ht]
      simp only [map_div, map_pow]
      rfl
    exact congrArg₂ (fun a b : GenericRing K => a * b) (congrArg Units.val hp) hx

/-- The published Fourier kernel becomes the exact existing AS source map. -/
theorem curve_kernel (s : (PhaseField K)ˣ) :
    curveMorphism K s ≫ universalKernelMorphism K = additiveMorphism K s := by
  dsimp only [curveMorphism, universalKernelMorphism, additiveMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (curve_kernelHom K s)

end PrimeGap182.TypeIII.FourierNormalizationMaps

#print axioms PrimeGap182.TypeIII.FourierNormalizationMaps.normalizationSquare_isPullback
#print axioms PrimeGap182.TypeIII.FourierNormalizationMaps.curve_projection
#print axioms PrimeGap182.TypeIII.FourierNormalizationMaps.curve_kernel
