import TypeIIIFiniteOriginFromRestriction

/-!
# Finite-sum Fourier compatibility from additivity on actual maps

Laumon's general local Fourier functor is additive on morphisms on its
continuous finite-coefficient admissible category. The comparison with a
finite direct sum is constructed from the actual inclusions and projections;
no separate isomorphism for those sums is assumed. Empty sums are included.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators

namespace PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps
open PublishedPhaseApplication PublishedLocalConstruction FiniteOriginFromRestriction

universe v w t
variable {E : Type v} [Field E] {I : Type w} [Group I] {G : Type t} [Group G]

section Sums
variable {ι : Type} [Fintype ι] (R : ι → FDRep E I)

/-- The literal direct-sum injection, including its equivariance. -/
def inclusion (i : ι) : Representation.IntertwiningMap (R i).ρ (finiteSum R).ρ where
  toLinearMap := DirectSum.lof E ι (fun i => (R i).V) i
  isIntertwining' g := by
    ext x
    exact (DirectSum.lmap_lof (fun i => (R i).ρ g) i x).symm

/-- The literal direct-sum coordinate projection. -/
def projection (i : ι) : Representation.IntertwiningMap (finiteSum R).ρ (R i).ρ where
  toLinearMap := DirectSum.component E ι (fun i => (R i).V) i
  isIntertwining' g := by
    change (DirectSum.component E ι (fun i => (R i).V) i).comp
        (DirectSum.lmap (fun i => (R i).ρ g)) = _
    apply DirectSum.linearMap_ext E
    intro j
    ext x
    change DirectSum.component E ι (fun i => (R i).V) i
        (DirectSum.lmap (fun i => (R i).ρ g) (DirectSum.lof E ι (fun i => (R i).V) j x)) = _
    rw [DirectSum.lmap_lof]
    by_cases h : j = i
    · subst j; simp
    · simp [DirectSum.component.of, h]

theorem projection_inclusion (i : ι) :
    (projection R i).comp (inclusion R i) = Representation.IntertwiningMap.id (R i).ρ := by
  ext x
  change DirectSum.component E ι (fun i => (R i).V) i
    (DirectSum.lof E ι (fun i => (R i).V) i x) = x
  rw [DirectSum.component.of]
  simp

theorem projection_inclusion_ne (i j : ι) (h : j ≠ i) :
    (projection R i).comp (inclusion R j) = 0 := by
  ext x
  change DirectSum.component E ι (fun i => (R i).V) i
    (DirectSum.lof E ι (fun i => (R i).V) j x) = 0
  rw [DirectSum.component.of]
  simp [h]

/-- This finite matrix identity also holds for the zero direct sum. -/
theorem sum_inclusion_projection :
    ∑ i, (inclusion R i).comp (projection R i) =
      Representation.IntertwiningMap.id (finiteSum R).ρ := by
  apply Representation.IntertwiningMap.ext
  apply DirectSum.linearMap_ext E
  intro j
  ext x
  change (∑ i, (inclusion R i).comp (projection R i))
    (DirectSum.lof E ι (fun i => (R i).V) j x) = DirectSum.lof E ι (fun i => (R i).V) j x
  simp only [Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.comp_apply]
  change (∑ i, DirectSum.lof E ι (fun i => (R i).V) i
    (DirectSum.component E ι (fun i => (R i).V) i
      (DirectSum.lof E ι (fun i => (R i).V) j x))) = _
  rw [Finset.sum_eq_single j]
  · rw [DirectSum.component.of]; simp
  · intro i _ hij
    rw [DirectSum.component.of]
    simp [Ne.symm hij]
  · intro h; exact (h (Finset.mem_univ j)).elim

/-- Assemble equivariant maps out of the actual direct sum. -/
def desc {V : FDRep E G} (S : ι → FDRep E G)
    (f : ∀ i, Representation.IntertwiningMap (S i).ρ V.ρ) :
    Representation.IntertwiningMap (finiteSum S).ρ V.ρ where
  toLinearMap := DirectSum.toModule E ι V.V (fun i => (f i).toLinearMap)
  isIntertwining' g := by
    change (DirectSum.toModule E ι V.V (fun i => (f i).toLinearMap)).comp
      (DirectSum.lmap (fun i => (S i).ρ g)) = _
    apply DirectSum.linearMap_ext E
    intro i
    ext x
    change DirectSum.toModule E ι V.V (fun i => (f i).toLinearMap)
      (DirectSum.lmap (fun i => (S i).ρ g) (DirectSum.lof E ι (fun i => (S i).V) i x)) = _
    rw [DirectSum.lmap_lof, DirectSum.toModule_lof]
    simpa only [LinearMap.comp_apply, DirectSum.toModule_lof] using
      congrArg (fun m => m x) ((f i).isIntertwining' g)

end Sums

variable {Admissible : FDRep E I → Prop}
  (F : AdmissibleRepresentationFunctor E I G Admissible)

/-- General admissibility closure and additivity on morphisms. There is
no field supplying a finite-sum comparison. -/
structure Rules : Prop where
  admissible_equiv : ∀ {R S : FDRep E I}, Representation.Equiv R.ρ S.ρ →
    Admissible R → Admissible S
  admissible_sum : ∀ {ι : Type} [Fintype ι], ∀ R : ι → FDRep E I,
    (∀ i, Admissible (R i)) → Admissible (finiteSum R)
  map_add : ∀ {R S : FDRep E I} (hR : Admissible R) (hS : Admissible S)
    (f g : Representation.IntertwiningMap R.ρ S.ρ),
    F.map hR hS (f + g) = F.map hR hS f + F.map hR hS g

variable {F} (A : Rules F)
include A

theorem Rules.map_zero {R S : FDRep E I} (hR : Admissible R) (hS : Admissible S) :
    F.map hR hS 0 = 0 := by
  have h := A.map_add hR hS 0 0
  rw [zero_add] at h
  exact (add_eq_left.mp h.symm)

def Rules.mapAddHom {R S : FDRep E I} (hR : Admissible R) (hS : Admissible S) :
    Representation.IntertwiningMap R.ρ S.ρ →+
      Representation.IntertwiningMap (F.obj R hR).ρ (F.obj S hS).ρ where
  toFun := F.map hR hS
  map_zero' := A.map_zero hR hS
  map_add' := A.map_add hR hS

variable {ι : Type} [Fintype ι] (R : ι → FDRep E I) (hR : ∀ i, Admissible (R i))

/-- The comparison uses Fourier images of the actual projections. -/
def Rules.toSum : Representation.IntertwiningMap
    (F.obj (finiteSum R) (A.admissible_sum R hR)).ρ
    (finiteSum (fun i => F.obj (R i) (hR i))).ρ :=
  ∑ i, (inclusion (fun i => F.obj (R i) (hR i)) i).comp
    (F.map (A.admissible_sum R hR) (hR i) (projection R i))

/-- Its inverse uses Fourier images of the actual inclusions. -/
def Rules.fromSum : Representation.IntertwiningMap
    (finiteSum (fun i => F.obj (R i) (hR i))).ρ
    (F.obj (finiteSum R) (A.admissible_sum R hR)).ρ :=
  desc (fun i => F.obj (R i) (hR i))
    (fun i => F.map (hR i) (A.admissible_sum R hR) (inclusion R i))

/-- The constructed inverse acts by the mapped original injection. -/
theorem Rules.fromSum_inclusion (i : ι) (x : F.obj (R i) (hR i)) :
    A.fromSum R hR (inclusion (fun i => F.obj (R i) (hR i)) i x) =
      F.map (hR i) (A.admissible_sum R hR) (inclusion R i) x := by
  change DirectSum.toModule E ι (F.obj (finiteSum R) (A.admissible_sum R hR)).V
    (fun i => (F.map (hR i) (A.admissible_sum R hR) (inclusion R i)).toLinearMap)
    (DirectSum.lof E ι (fun i => (F.obj (R i) (hR i)).V) i x) = _
  exact DirectSum.toModule_lof E
    (φ := fun i => (F.map (hR i) (A.admissible_sum R hR) (inclusion R i)).toLinearMap) i x

/-- Additivity sends the original sum of matrix idempotents to identity. -/
theorem Rules.mapped_resolution :
    ∑ i, (F.map (hR i) (A.admissible_sum R hR) (inclusion R i)).comp
      (F.map (A.admissible_sum R hR) (hR i) (projection R i)) =
      Representation.IntertwiningMap.id (F.obj (finiteSum R) (A.admissible_sum R hR)).ρ := by
  simp_rw [← F.map_comp]
  change (∑ i, A.mapAddHom _ _ ((inclusion R i).comp (projection R i))) = _
  rw [← map_sum, sum_inclusion_projection]
  exact F.map_id _ _

/-- The two maps are inverse on the Fourier image of the original sum. -/
theorem Rules.fromSum_toSum : (A.fromSum R hR).comp (A.toSum R hR) =
    Representation.IntertwiningMap.id (F.obj (finiteSum R) (A.admissible_sum R hR)).ρ := by
  ext x
  change A.fromSum R hR ((A.toSum R hR) x) = x
  simp only [Rules.toSum, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.comp_apply, map_sum, Rules.fromSum_inclusion]
  have h := congrArg (fun f => f x) (A.mapped_resolution R hR)
  simpa only [Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.id_apply] using h

/-- The other composite is identity, checked on each actual summand. -/
theorem Rules.toSum_fromSum : (A.toSum R hR).comp (A.fromSum R hR) =
    Representation.IntertwiningMap.id (finiteSum (fun i => F.obj (R i) (hR i))).ρ := by
  apply Representation.IntertwiningMap.ext
  apply DirectSum.linearMap_ext E
  intro j
  ext x
  change A.toSum R hR (A.fromSum R hR (inclusion (fun i => F.obj (R i) (hR i)) j x)) =
    inclusion (fun i => F.obj (R i) (hR i)) j x
  rw [A.fromSum_inclusion]
  simp only [Rules.toSum, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.comp_apply]
  rw [Finset.sum_eq_single j]
  · have h := F.map_comp (hR j) (A.admissible_sum R hR) (hR j)
      (inclusion R j) (projection R j)
    rw [projection_inclusion, F.map_id] at h
    have hx := congrArg (fun f => f x) h
    exact congrArg (inclusion (fun i => F.obj (R i) (hR i)) j) hx.symm
  · intro i _ hij
    have h := F.map_comp (hR j) (A.admissible_sum R hR) (hR i)
      (inclusion R j) (projection R i)
    rw [projection_inclusion_ne R i j (Ne.symm hij), A.map_zero] at h
    have hx := congrArg (fun f => f x) h
    change inclusion (fun i => F.obj (R i) (hR i)) i
      (((F.map _ _ (projection R i)).comp (F.map _ _ (inclusion R j))) x) = 0
    rw [← hx]
    simp
  · intro h; exact (h (Finset.mem_univ j)).elim

/-- The finite-sum equivalence is built from these maps and their proved
inverse identities, on the full admissible domain. -/
def Rules.sumEquiv : Representation.Equiv
    (F.obj (finiteSum R) (A.admissible_sum R hR)).ρ
    (finiteSum (fun i => F.obj (R i) (hR i))).ρ where
  toLinearEquiv := LinearEquiv.ofLinearMap (A.toSum R hR).toLinearMap
    (A.fromSum R hR).toLinearMap
    (congrArg (fun f => f.toLinearMap) (A.toSum_fromSum R hR))
    (congrArg (fun f => f.toLinearMap) (A.fromSum_toSum R hR))
  isIntertwining' := (A.toSum R hR).isIntertwining'

/-- Supply the preceding unscaled interface with the proved sum comparison. -/
def Rules.unscaledAdditivity : UnscaledAdditivity F where
  admissible_equiv := A.admissible_equiv
  admissible_sum := A.admissible_sum
  sum := A.sumEquiv

end PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps


#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.inclusion
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.projection
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.projection_inclusion
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.projection_inclusion_ne
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.sum_inclusion_projection
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.desc
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.map_zero
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.mapAddHom
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.fromSum_inclusion
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.mapped_resolution
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.fromSum_toSum
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.toSum_fromSum
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.sumEquiv
#print axioms PrimeGap182.TypeIII.LocalFourierFromAdditiveMaps.Rules.unscaledAdditivity
