import TypeIIIKloostermanPhaseFamily

/-!
# Actual points of the Kloosterman phase family

The fixed ring F_p[t,u,u⁻¹,v,v⁻¹] has the literal universal property
suggested by its coordinates. A homomorphism to a field is uniquely
determined by the value of t and the two unit values of u and v.

The proof uses uniqueness for Laurent localization and the fact that
ring homomorphisms from ZMod p are unique. No point parametrization is
assumed. The associated spectrum comparison identifies the actual
points over a fixed parameter with the two-dimensional unit torus.
-/

noncomputable section

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

/-- A Laurent polynomial ring homomorphism is determined by its
coefficient map and the image of the invertible variable. -/
theorem laurentPolynomial_ringHom_ext {R S : Type*} [CommRing R] [CommRing S]
    {g h : LaurentPolynomial R →+* S}
    (hC : ∀ r, g (LaurentPolynomial.C r) = h (LaurentPolynomial.C r))
    (hT : g (LaurentPolynomial.T 1) = h (LaurentPolynomial.T 1)) : g = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C] using hC r
  · simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X] using hT

/-- The first torus coordinate is an actual unit of the phase ring. -/
def kloostermanPhaseUnitU (p : ℕ) : (KloostermanPhaseRing p)ˣ :=
  Units.map LaurentPolynomial.C.toMonoidHom
    (unitOfInvertible (LaurentPolynomial.T 1 :
      LaurentPolynomial (Polynomial (ZMod p))))

/-- The second torus coordinate is an actual unit of the phase ring. -/
def kloostermanPhaseUnitV (p : ℕ) : (KloostermanPhaseRing p)ˣ :=
  unitOfInvertible (LaurentPolynomial.T 1)

@[simp] theorem kloostermanPhaseUnitU_val (p : ℕ) :
    (kloostermanPhaseUnitU p : KloostermanPhaseRing p) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) := rfl

@[simp] theorem kloostermanPhaseUnitV_val (p : ℕ) :
    (kloostermanPhaseUnitV p : KloostermanPhaseRing p) =
      LaurentPolynomial.T 1 := rfl

/-- All three coordinate values determine a ring homomorphism from the
actual phase ring; compatibility on prime-field constants is automatic. -/
theorem kloostermanPhaseRingHom_ext (p : ℕ) {K : Type*} [CommRing K]
    {g h : KloostermanPhaseRing p →+* K}
    (ht : g (kloostermanPhaseParameterHom p Polynomial.X) =
      h (kloostermanPhaseParameterHom p Polynomial.X))
    (hu : g (kloostermanPhaseUnitU p) = h (kloostermanPhaseUnitU p))
    (hv : g (kloostermanPhaseUnitV p) = h (kloostermanPhaseUnitV p)) : g = h := by
  apply laurentPolynomial_ringHom_ext ?_ hv
  have hinner : g.comp LaurentPolynomial.C = h.comp LaurentPolynomial.C := by
    apply laurentPolynomial_ringHom_ext ?_ hu
    have hparameter : g.comp (kloostermanPhaseParameterHom p) =
        h.comp (kloostermanPhaseParameterHom p) :=
      Polynomial.ringHom_ext' (Subsingleton.elim _ _) ht
    exact fun q => RingHom.congr_fun hparameter q
  exact fun q => RingHom.congr_fun hinner q

section FieldPoints

variable (p : ℕ) (K : Type) [Field K] [Algebra (ZMod p) K]

/-- Reading the three actual coordinates of a phase-ring point. -/
def kloostermanPhaseRingHomCoordinates (g : KloostermanPhaseRing p →+* K) :
    K × (Kˣ × Kˣ) :=
  (g (kloostermanPhaseParameterHom p Polynomial.X),
    Units.map g.toMonoidHom (kloostermanPhaseUnitU p),
    Units.map g.toMonoidHom (kloostermanPhaseUnitV p))

@[simp] theorem kloostermanPhaseEvaluation_unitU (t : K) (u v : Kˣ) :
    Units.map (kloostermanPhaseEvaluation p K t u v).toMonoidHom
      (kloostermanPhaseUnitU p) = u := by
  apply Units.ext
  change kloostermanPhaseEvaluation p K t u v
    (LaurentPolynomial.C (LaurentPolynomial.T 1)) = (u : K)
  simp only [kloostermanPhaseEvaluation, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T, zpow_one]

@[simp] theorem kloostermanPhaseEvaluation_unitV (t : K) (u v : Kˣ) :
    Units.map (kloostermanPhaseEvaluation p K t u v).toMonoidHom
      (kloostermanPhaseUnitV p) = v := by
  apply Units.ext
  change kloostermanPhaseEvaluation p K t u v (LaurentPolynomial.T 1) = (v : K)
  simp only [kloostermanPhaseEvaluation, LaurentPolynomial.eval₂_T, zpow_one]

/-- Evaluating at a triple and then reading the coordinates returns
that same triple, including its specified unit structures. -/
@[simp] theorem kloostermanPhaseRingHomCoordinates_evaluation (t : K) (u v : Kˣ) :
    kloostermanPhaseRingHomCoordinates p K (kloostermanPhaseEvaluation p K t u v) =
      (t, u, v) := by
  simp only [kloostermanPhaseRingHomCoordinates, kloostermanPhaseEvaluation_parameter,
    Polynomial.eval₂_X, kloostermanPhaseEvaluation_unitU, kloostermanPhaseEvaluation_unitV]

/-- Every homomorphism is precisely the existing Laurent evaluation
at its three coordinate values. -/
theorem kloostermanPhaseEvaluation_coordinates (g : KloostermanPhaseRing p →+* K) :
    kloostermanPhaseEvaluation p K (kloostermanPhaseRingHomCoordinates p K g).1
      (kloostermanPhaseRingHomCoordinates p K g).2.1
      (kloostermanPhaseRingHomCoordinates p K g).2.2 = g := by
  apply kloostermanPhaseRingHom_ext p
  · simp only [kloostermanPhaseEvaluation_parameter, Polynomial.eval₂_X,
      kloostermanPhaseRingHomCoordinates]
  · have h := congrArg Units.val (kloostermanPhaseEvaluation_unitU p K
      (kloostermanPhaseRingHomCoordinates p K g).1
      (kloostermanPhaseRingHomCoordinates p K g).2.1
      (kloostermanPhaseRingHomCoordinates p K g).2.2)
    exact h
  · have h := congrArg Units.val (kloostermanPhaseEvaluation_unitV p K
      (kloostermanPhaseRingHomCoordinates p K g).1
      (kloostermanPhaseRingHomCoordinates p K g).2.1
      (kloostermanPhaseRingHomCoordinates p K g).2.2)
    exact h

/-- The actual universal property of F_p[t,u,u⁻¹,v,v⁻¹]. Its inverse
is the phase evaluation already used by the geometric trace integrand. -/
def kloostermanPhaseRingHomEquiv :
    (KloostermanPhaseRing p →+* K) ≃ K × (Kˣ × Kˣ) where
  toFun := kloostermanPhaseRingHomCoordinates p K
  invFun x := kloostermanPhaseEvaluation p K x.1 x.2.1 x.2.2
  left_inv := kloostermanPhaseEvaluation_coordinates p K
  right_inv x := kloostermanPhaseRingHomCoordinates_evaluation p K x.1 x.2.1 x.2.2

@[simp] theorem kloostermanPhaseRingHomEquiv_symm_apply (t : K) (u v : Kˣ) :
    (kloostermanPhaseRingHomEquiv p K).symm (t, u, v) =
      kloostermanPhaseEvaluation p K t u v := rfl

/-- All actual K-valued points of the fixed affine phase scheme are
parametrized by one field coordinate and two unit coordinates. -/
def kloostermanPhaseSchemePointEquiv :
    (Spec (.of K) ⟶ kloostermanPhaseScheme p) ≃ K × (Kˣ × Kˣ) where
  toFun x := kloostermanPhaseRingHomCoordinates p K (Spec.preimage x).hom
  invFun x := kloostermanPhaseSchemePoint p K x.1 x.2.1 x.2.2
  left_inv x := by
    change Spec.map (CommRingCat.ofHom
      (kloostermanPhaseEvaluation p K
        (kloostermanPhaseRingHomCoordinates p K (Spec.preimage x).hom).1
        (kloostermanPhaseRingHomCoordinates p K (Spec.preimage x).hom).2.1
        (kloostermanPhaseRingHomCoordinates p K (Spec.preimage x).hom).2.2)) = x
    rw [kloostermanPhaseEvaluation_coordinates]
    exact Spec.map_preimage x
  right_inv x := by
    change kloostermanPhaseRingHomCoordinates p K
      (Spec.preimage (kloostermanPhaseSchemePoint p K x.1 x.2.1 x.2.2)).hom = x
    dsimp only [kloostermanPhaseSchemePoint]
    rw [Spec.preimage_map]
    exact kloostermanPhaseRingHomCoordinates_evaluation p K x.1 x.2.1 x.2.2

@[simp] theorem kloostermanPhaseSchemePointEquiv_symm_apply (t : K) (u v : Kˣ) :
    (kloostermanPhaseSchemePointEquiv p K).symm (t, u, v) =
      kloostermanPhaseSchemePoint p K t u v := rfl

@[simp] theorem kloostermanPhaseSchemePointEquiv_point (t : K) (u v : Kˣ) :
    kloostermanPhaseSchemePointEquiv p K (kloostermanPhaseSchemePoint p K t u v) =
      (t, u, v) :=
  (kloostermanPhaseSchemePointEquiv p K).apply_symm_apply (t, u, v)

/-- The actual commuting triangle over the parameter line is equivalent
to fixing the first coordinate of the point parametrization. -/
theorem kloostermanPhaseSchemePointEquiv_over_iff
    (x : Spec (.of K) ⟶ kloostermanPhaseScheme p) (t : K) :
    x ≫ kloostermanPhaseProjection p =
        Spec.map (CommRingCat.ofHom
          (Polynomial.eval₂RingHom (algebraMap (ZMod p) K) t)) ↔
      (kloostermanPhaseSchemePointEquiv p K x).1 = t := by
  constructor
  · intro hx
    have hhom : CommRingCat.ofHom (kloostermanPhaseParameterHom p) ≫ Spec.preimage x =
        CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap (ZMod p) K) t) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hx
    have hX := congrArg
      (fun q : CommRingCat.of (Polynomial (ZMod p)) ⟶ CommRingCat.of K =>
        q.hom Polynomial.X) hhom
    change (Spec.preimage x).hom (kloostermanPhaseParameterHom p Polynomial.X) =
      Polynomial.eval₂ (algebraMap (ZMod p) K) t Polynomial.X at hX
    exact hX.trans (Polynomial.eval₂_X _ _)
  · intro ht
    have hx : kloostermanPhaseSchemePoint p K
        (kloostermanPhaseSchemePointEquiv p K x).1
        (kloostermanPhaseSchemePointEquiv p K x).2.1
        (kloostermanPhaseSchemePointEquiv p K x).2.2 = x :=
      (kloostermanPhaseSchemePointEquiv p K).symm_apply_apply x
    rw [← hx, kloostermanPhaseSchemePoint_over, ht]

/-- The actual K-valued points of the phase scheme whose projection is
the K-valued parameter t, specified by their commuting scheme diagram. -/
abbrev KloostermanPhaseSchemeFiber (t : K) :=
  {x : Spec (.of K) ⟶ kloostermanPhaseScheme p //
    x ≫ kloostermanPhaseProjection p =
      Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom (algebraMap (ZMod p) K) t))}

/-- The full actual fiber over t is the two-dimensional unit torus.
The inverse sends (u,v) to the existing point defined by Laurent evaluation. -/
def kloostermanPhaseSchemeFiberEquiv (t : K) :
    KloostermanPhaseSchemeFiber p K t ≃ Kˣ × Kˣ where
  toFun x := (kloostermanPhaseSchemePointEquiv p K x.val).2
  invFun uv := ⟨kloostermanPhaseSchemePoint p K t uv.1 uv.2,
    kloostermanPhaseSchemePoint_over p K t uv.1 uv.2⟩
  left_inv x := by
    apply Subtype.ext
    apply (kloostermanPhaseSchemePointEquiv p K).injective
    change kloostermanPhaseSchemePointEquiv p K
      (kloostermanPhaseSchemePoint p K t
        (kloostermanPhaseSchemePointEquiv p K x.val).2.1
        (kloostermanPhaseSchemePointEquiv p K x.val).2.2) =
      kloostermanPhaseSchemePointEquiv p K x.val
    rw [kloostermanPhaseSchemePointEquiv_point]
    exact Prod.ext
      ((kloostermanPhaseSchemePointEquiv_over_iff p K x.val t).mp x.property).symm rfl
  right_inv uv := by
    change (kloostermanPhaseSchemePointEquiv p K
      (kloostermanPhaseSchemePoint p K t uv.1 uv.2)).2 = uv
    rw [kloostermanPhaseSchemePointEquiv_point]

@[simp] theorem kloostermanPhaseSchemeFiberEquiv_symm_val (t : K) (u v : Kˣ) :
    ((kloostermanPhaseSchemeFiberEquiv p K t).symm (u, v)).val =
      kloostermanPhaseSchemePoint p K t u v := rfl

end FieldPoints

end PrimeGap182.TypeIII

#print axioms PrimeGap182.TypeIII.laurentPolynomial_ringHom_ext
#print axioms PrimeGap182.TypeIII.kloostermanPhaseUnitU
#print axioms PrimeGap182.TypeIII.kloostermanPhaseUnitV
#print axioms PrimeGap182.TypeIII.kloostermanPhaseUnitU_val
#print axioms PrimeGap182.TypeIII.kloostermanPhaseUnitV_val
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRingHom_ext
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRingHomCoordinates
#print axioms PrimeGap182.TypeIII.kloostermanPhaseEvaluation_unitU
#print axioms PrimeGap182.TypeIII.kloostermanPhaseEvaluation_unitV
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRingHomCoordinates_evaluation
#print axioms PrimeGap182.TypeIII.kloostermanPhaseEvaluation_coordinates
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRingHomEquiv
#print axioms PrimeGap182.TypeIII.kloostermanPhaseRingHomEquiv_symm_apply
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemePointEquiv
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemePointEquiv_symm_apply
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemePointEquiv_point
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemePointEquiv_over_iff
#print axioms PrimeGap182.TypeIII.KloostermanPhaseSchemeFiber
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemeFiberEquiv
#print axioms PrimeGap182.TypeIII.kloostermanPhaseSchemeFiberEquiv_symm_val
