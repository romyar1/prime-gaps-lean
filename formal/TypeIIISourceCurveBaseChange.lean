import TypeIIIGenericSourceSpecialization
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The original source curve is a relative Laurent line

The universal property is proved in commutative rings, including targets
with nilpotents. It identifies the actual parameter projection's base
change with a Laurent polynomial ring, hence gives a Cartesian square of
schemes. No sheaf base-change statement is assumed in this algebraic step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open scoped Classical

namespace PrimeGap182.TypeIII.SourceCurveBaseChange

open StartingSourceMaps PhysicalTorusLaurent GenericSourceSpecialization

universe u
variable (K : Type u) [Field K]

/-- The quotient's three units and its coefficient field determine any
ring map; this is not restricted to maps into fields. -/
theorem source_ringHom_ext {R : Type u} [CommRing R] {f g : SourceRing K →+* R}
    (hc : ∀ c, f (algebraMap K (SourceRing K) c) = g (algebraMap K (SourceRing K) c))
    (hu : ∀ i, Units.map f.toMonoidHom (coordinateUnit K i) = Units.map g.toMonoidHom (coordinateUnit K i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    exact hc c
  · intro i
    have h0 := congrArg Units.val (hu 0)
    have h1 := congrArg (fun x : Rˣ => (x⁻¹).val) (hu 0)
    have h2 := congrArg Units.val (hu 1)
    have h3 := congrArg (fun x : Rˣ => (x⁻¹).val) (hu 1)
    have h4 := congrArg Units.val (hu 2)
    have h5 := congrArg (fun x : Rˣ => (x⁻¹).val) (hu 2)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-- Over the parameter ring only the curve coordinate remains free. -/
theorem source_ringHom_ext_over_parameters {R : Type u} [CommRing R]
    {f g : SourceRing K →+* R}
    (hp : f.comp (CanonicalCurveInput.parameterHom K).toRingHom =
      g.comp (CanonicalCurveInput.parameterHom K).toRingHom)
    (hx : Units.map f.toMonoidHom (coordinateUnit K 0) = Units.map g.toMonoidHom (coordinateUnit K 0)) : f = g := by
  apply source_ringHom_ext K
  · intro c
    have h := DFunLike.congr_fun hp (algebraMap K (PhysicalTorusMorphism.TorusRing K) c)
    change f ((CanonicalCurveInput.parameterHom K)
      (algebraMap K (PhysicalTorusMorphism.TorusRing K) c)) =
      g ((CanonicalCurveInput.parameterHom K)
        (algebraMap K (PhysicalTorusMorphism.TorusRing K) c)) at h
    rw [AlgHom.commutes] at h
    exact h
  · intro i
    have hl := congrArg (fun q : PhysicalTorusMorphism.TorusRing K →+* R =>
      Units.map q.toMonoidHom (PhysicalTorusMorphism.xUnit K)) hp
    have ht := congrArg (fun q : PhysicalTorusMorphism.TorusRing K →+* R =>
      Units.map q.toMonoidHom (PhysicalTorusMorphism.yUnit K)) hp
    change Units.map f.toMonoidHom (Units.map (CanonicalCurveInput.parameterHom K).toRingHom.toMonoidHom
      (PhysicalTorusMorphism.xUnit K)) = Units.map g.toMonoidHom
      (Units.map (CanonicalCurveInput.parameterHom K).toRingHom.toMonoidHom (PhysicalTorusMorphism.xUnit K)) at hl
    change Units.map f.toMonoidHom (Units.map (CanonicalCurveInput.parameterHom K).toRingHom.toMonoidHom
      (PhysicalTorusMorphism.yUnit K)) = Units.map g.toMonoidHom
      (Units.map (CanonicalCurveInput.parameterHom K).toRingHom.toMonoidHom (PhysicalTorusMorphism.yUnit K)) at ht
    have hpx : Units.map (CanonicalCurveInput.parameterHom K).toRingHom.toMonoidHom
        (PhysicalTorusMorphism.xUnit K) = coordinateUnit K 1 :=
      CanonicalCurveInput.parameterHom_xUnit K
    have hpy : Units.map (CanonicalCurveInput.parameterHom K).toRingHom.toMonoidHom
        (PhysicalTorusMorphism.yUnit K) = coordinateUnit K 2 :=
      CanonicalCurveInput.parameterHom_yUnit K
    rw [hpx] at hl
    rw [hpy] at ht
    fin_cases i
    · exact hx
    · exact hl
    · exact ht

variable {A : Type u} [CommRing A] [Algebra K A]

def coefficientHom : A →ₐ[K] LaurentPolynomial A where
  toRingHom := LaurentPolynomial.C
  commutes' _ := rfl

variable (p : PhysicalTorusMorphism.TorusRing K →ₐ[K] A)

def sourceMap : SourceRing K →ₐ[K] LaurentPolynomial A :=
  StartingSourceMaps.evaluation (variableUnit A)
    (Units.map ((coefficientHom K).comp p).toRingHom (PhysicalTorusMorphism.xUnit K))
    (Units.map ((coefficientHom K).comp p).toRingHom (PhysicalTorusMorphism.yUnit K))

theorem sourceMap_coordinateUnit (i : Fin 3) :
    Units.map (sourceMap K p).toRingHom (coordinateUnit K i) =
      ![variableUnit A,
        Units.map ((coefficientHom K).comp p).toRingHom (PhysicalTorusMorphism.xUnit K),
        Units.map ((coefficientHom K).comp p).toRingHom (PhysicalTorusMorphism.yUnit K)] i :=
  evaluation_coordinateUnit K _ _ _ i

theorem sourceMap_parameter :
    (sourceMap K p).comp (CanonicalCurveInput.parameterHom K) = (coefficientHom K).comp p := by
  have h := PhysicalTorusLaurent.evaluation_natural K (sourceMap K p)
    (coordinateUnit K 1) (coordinateUnit K 2)
  change (sourceMap K p).comp (CanonicalCurveInput.parameterHom K) = _ at h
  have h' := PhysicalTorusLaurent.evaluation_natural K ((coefficientHom K).comp p)
    (PhysicalTorusMorphism.xUnit K) (PhysicalTorusMorphism.yUnit K)
  rw [PhysicalTorusLaurent.evaluation_identity, AlgHom.comp_id] at h'
  exact h.trans ((congrArg₂
    (PhysicalTorusMorphism.evaluation (K := K) (A := LaurentPolynomial A))
    (sourceMap_coordinateUnit K p 1) (sourceMap_coordinateUnit K p 2)).trans h'.symm)

/-- Coefficients and the invertible variable determine a Laurent ring map. -/
theorem laurent_ringHom_ext {B R : Type u} [CommRing B] [CommRing R]
    {f g : LaurentPolynomial B →+* R}
    (hc : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C)
    (hx : Units.map f.toMonoidHom (variableUnit B) =
      Units.map g.toMonoidHom (variableUnit B)) : f = g := by
  have hn (n : ℤ) : f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    have h := congrArg (fun t : Rˣ => (t ^ n).val) hx
    simp only [← map_zpow] at h
    change f ((variableUnit B ^ n : (LaurentPolynomial B)ˣ).val) =
      g ((variableUnit B ^ n : (LaurentPolynomial B)ˣ).val) at h
    simpa only [variableUnit_pow] using h
  apply RingHom.ext
  intro a
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | C_mul_T n c =>
    rw [map_mul, map_mul, hn]
    exact congrArg (fun t : R => t * g (LaurentPolynomial.T n)) (DFunLike.congr_fun hc c)

variable {R : Type u} [CommRing R]

/-- The unique candidate extension of a compatible pair of ring maps. -/
def liftMap (f : SourceRing K →+* R) (g : A →+* R) : LaurentPolynomial A →+* R :=
  LaurentPolynomial.eval₂ g (Units.map f.toMonoidHom (coordinateUnit K 0))

theorem liftMap_coefficients (f : SourceRing K →+* R) (g : A →+* R) :
    (liftMap K f g).comp (coefficientHom K).toRingHom = g := by
  apply RingHom.ext
  intro a
  exact LaurentPolynomial.eval₂_C _ _ a

omit [Algebra K A] in
theorem liftMap_variable (f : SourceRing K →+* R) (g : A →+* R) :
    Units.map (liftMap K f g).toMonoidHom (variableUnit A) =
      Units.map f.toMonoidHom (coordinateUnit K 0) := by
  apply Units.ext
  change LaurentPolynomial.eval₂ g (Units.map f.toMonoidHom (coordinateUnit K 0))
    (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

theorem liftMap_source (f : SourceRing K →+* R) (g : A →+* R)
    (h : f.comp (CanonicalCurveInput.parameterHom K).toRingHom = g.comp p.toRingHom) :
    (liftMap K f g).comp (sourceMap K p).toRingHom = f := by
  apply source_ringHom_ext_over_parameters K
  · have hs := congrArg AlgHom.toRingHom (sourceMap_parameter K p)
    change (sourceMap K p).toRingHom.comp (CanonicalCurveInput.parameterHom K).toRingHom =
      (coefficientHom K).toRingHom.comp p.toRingHom at hs
    rw [RingHom.comp_assoc, hs, ← RingHom.comp_assoc, liftMap_coefficients]
    exact h.symm
  · change Units.map (liftMap K f g).toMonoidHom
      (Units.map (sourceMap K p).toRingHom.toMonoidHom (coordinateUnit K 0)) = _
    have hx := sourceMap_coordinateUnit K p 0
    change Units.map (sourceMap K p).toRingHom.toMonoidHom (coordinateUnit K 0) =
      variableUnit A at hx
    rw [hx]
    exact liftMap_variable K f g

theorem liftMap_unique (f : SourceRing K →+* R) (g : A →+* R)
    (q : LaurentPolynomial A →+* R)
    (hf : q.comp (sourceMap K p).toRingHom = f)
    (hg : q.comp (coefficientHom K).toRingHom = g) : q = liftMap K f g := by
  apply laurent_ringHom_ext
  · exact hg.trans (liftMap_coefficients K f g).symm
  · have h := congrArg (fun t : SourceRing K →+* R =>
      Units.map t.toMonoidHom (coordinateUnit K 0)) hf
    change Units.map q.toMonoidHom
      (Units.map (sourceMap K p).toRingHom.toMonoidHom (coordinateUnit K 0)) = _ at h
    have hx := sourceMap_coordinateUnit K p 0
    change Units.map (sourceMap K p).toRingHom.toMonoidHom (coordinateUnit K 0) =
      variableUnit A at hx
    rw [hx] at h
    exact h.trans (liftMap_variable K f g).symm

/-- The Laurent curve satisfies the full pushout universal property in
commutative rings, with the original parameter projection. -/
theorem sourceSquare_isPushout :
    IsPushout (CommRingCat.ofHom (CanonicalCurveInput.parameterHom K).toRingHom)
      (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom (sourceMap K p).toRingHom)
      (CommRingCat.ofHom (coefficientHom K (A := A)).toRingHom) := by
  have h : CommRingCat.ofHom (CanonicalCurveInput.parameterHom K).toRingHom ≫
      CommRingCat.ofHom (sourceMap K p).toRingHom =
      CommRingCat.ofHom p.toRingHom ≫ CommRingCat.ofHom (coefficientHom K).toRingHom :=
    congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom (sourceMap_parameter K p))
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk h
    (fun s => CommRingCat.ofHom (liftMap K s.inl.hom s.inr.hom)) ?_ ?_ ?_)
  · intro s
    apply CommRingCat.hom_ext
    exact liftMap_source K p s.inl.hom s.inr.hom (congrArg CommRingCat.Hom.hom s.condition)
  · intro s
    apply CommRingCat.hom_ext
    exact liftMap_coefficients K s.inl.hom s.inr.hom
  · intro s q hf hg
    apply CommRingCat.hom_ext
    exact liftMap_unique K p s.inl.hom s.inr.hom q.hom
      (congrArg CommRingCat.Hom.hom hf) (congrArg CommRingCat.Hom.hom hg)

/-- The corresponding square of actual affine schemes is Cartesian. -/
theorem sourceSquare_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (sourceMap K p).toRingHom))
      (Spec.map (CommRingCat.ofHom (coefficientHom K (A := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (CanonicalCurveInput.parameterHom K).toRingHom))
      (Spec.map (CommRingCat.ofHom p.toRingHom)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (sourceSquare_isPushout K p)

end PrimeGap182.TypeIII.SourceCurveBaseChange

#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.source_ringHom_ext_over_parameters
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.sourceMap_parameter
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.source_ringHom_ext
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.sourceMap_coordinateUnit
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.laurent_ringHom_ext
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.liftMap_coefficients
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.liftMap_variable
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.liftMap_source
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.liftMap_unique
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.sourceSquare_isPushout
#print axioms PrimeGap182.TypeIII.SourceCurveBaseChange.sourceSquare_isPullback
