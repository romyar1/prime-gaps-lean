import TypeIIIPerverseLinearPullbackFromExactInverseImages
import TypeIIICanonicalAffineCoefficientChange

/-!
# Native surface dimensions from actual geometric points

The plane is the SAME native perverse full subcategory used by linear
pullback and radial inertia. Geometric point maps are literal evaluations
Spec k -> A2_k, with BOTH affine origins retained. Ordinary H^(-2),H^(-1),H^0
after SAME-A point inverse image and one ordinary coefficient-fiber functor
define the three original dimensions. Their nonzero union defines support.
The remaining Jordan--Hölder list, purity, simplicity and geometric QST
complexity are general observables on these fixed native objects.

The intended bounded-constructible adic perverse interpretation, finite
geometric stalks and absence of ordinary stalk degrees outside [-2,0]
remain explicit general model scope. This module does not prove BBD/QST
laws or instantiate the whole compatible input family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical

namespace PrimeGap182.TypeIII.NativeSurfaceFromGeometricStalks
open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages PublishedSupportRules

universe w
variable (k : Type) [Field k]

abbrev pointScheme : Scheme := Spec (.of k)

def pointHom (z : k × k) : MvPolynomial (Fin 2) k →+* k :=
  MvPolynomial.eval ![z.1, z.2]

def pointMorphism (z : k × k) : pointScheme k ⟶
    FullFourierKernelCoordinates.planeScheme k :=
  Spec.map (CommRingCat.ofHom (pointHom k z))

def linePointHom (x : k) : MvPolynomial (Fin 1) k →+* k :=
  MvPolynomial.eval (fun _ => x)

def linePointMorphism (x : k) : pointScheme k ⟶
    LocalFourierKernelCoordinates.affineLine k :=
  Spec.map (CommRingCat.ofHom (linePointHom k x))

theorem point_linearHom (z : k × k) (a b : k) :
    (pointHom k z).comp (LinearRadialPhaseFromPoleTransport.linearHom a b).toRingHom =
      linePointHom k (a * z.1 + b * z.2) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [pointHom, linePointHom, LinearRadialPhaseFromPoleTransport.linearHom]
  · intro i
    simp [pointHom, linePointHom, LinearRadialPhaseFromPoleTransport.linearHom]

theorem point_linearMorphism (z : k × k) (a b : k) :
    pointMorphism k z ≫ LinearRadialPhaseFromPoleTransport.linearMorphism a b =
      linePointMorphism k (a * z.1 + b * z.2) := by
  dsimp only [pointMorphism, LinearRadialPhaseFromPoleTransport.linearMorphism,
    linePointMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (point_linearHom k z a b)

variable {K0 k J : Type} [Field K0] [Field k]
  {B : SourceInverseImageSystem.System.{0,w} K0}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{w} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{w} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{w} (OC i)] [∀ i, Abelian (OC i)]
  (A : OrdinarySystem (extensionScheme (extraScheme k otherScheme))
    (extensionObjects B (extraObjects NC LC OC)))

local instance commonLocalizations : ∀ i,
    HasDerivedCategory.{w} (extensionObjects B (extraObjects NC LC OC) i) :=
  fun i => HasDerivedCategory.standard (extensionObjects B (extraObjects NC LC OC) i)

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{w} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

def pointIndex (j : J) : CommonIndex (K0 := K0) (J := J) :=
  Sum.inr (Sum.inr (Sum.inr j))

variable {A} (D : Admissibility A) (point : J)
  (hPoint : otherScheme point = pointScheme k)

/-- The ACTUAL geometric point map in the SAME indexed ordinary system. -/
def indexedPointMorphism (z : k × k) :
    extensionScheme (K := K0) (extraScheme k otherScheme) (pointIndex (K0 := K0) point) ⟶
      extensionScheme (K := K0) (extraScheme k otherScheme) (nativeIndex .plane) :=
  eqToHom hPoint ≫ pointMorphism k z

variable {E : Type} [Field E] (fiber : OC point ⥤ ModuleCat.{w} E)

/-- Ordinary point cohomology from the fixed native inverse image. -/
def pointCohomologyFunctor (z : k × k) (n : ℤ) : Obj D ⥤ ModuleCat.{w} E :=
  D.plane.ι ⋙ A.derivedPull (i := pointIndex point) (j := nativeIndex .plane)
    (indexedPointMorphism point hPoint z) ⋙ A.ordinary (pointIndex point) n ⋙ fiber

def pointCohomology (Q : Obj D) (z : k × k) (n : ℤ) : ModuleCat.{w} E :=
  (pointCohomologyFunctor D point hPoint fiber z n).obj Q

/-- Precisely the original ordinary degree indices -2,-1,0. -/
def ordinaryDegree (i : Fin 3) : ℤ := (i.val : ℤ) - 2

def geometricDimension (Q : Obj D) (z : k × k) (i : Fin 3) : ℕ :=
  Module.finrank E (pointCohomology D point hPoint fiber Q z (ordinaryDegree i))

/-- Actual nonzero-stalk support in the three perverse ordinary degrees. -/
def geometricSupport (Q : Obj D) : Set (k × k) :=
  {z | ∃ i : Fin 3, geometricDimension D point hPoint fiber Q z i ≠ 0}

/-- General bounded-constructible perverse point-stalk facts, on EVERY
native object and geometric point. No support exclusion is assumed. -/
structure StalkLaws : Prop where
  finite : ∀ Q z n, FiniteDimensional E (pointCohomology D point hPoint fiber Q z n)
  outside : ∀ Q z n, n < -2 ∨ 0 < n →
    Subsingleton (pointCohomology D point hPoint fiber Q z n)

variable {D point hPoint fiber} (L : StalkLaws D point hPoint fiber)

include L in
/-- The three recorded degrees recover FULL ordinary nonzero-stalk
support using the general perverse amplitude and stalk finiteness. -/
theorem geometricSupport_eq_full (Q : Obj D) :
    geometricSupport D point hPoint fiber Q =
      {z | ∃ n : ℤ, Nontrivial (pointCohomology D point hPoint fiber Q z n)} := by
  ext z
  constructor
  · rintro ⟨i, hi⟩
    let := L.finite Q z (ordinaryDegree i)
    exact ⟨ordinaryDegree i, Module.finrank_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hi)⟩
  · rintro ⟨n, hn⟩
    have hRange : -2 ≤ n ∧ n ≤ 0 := by
      by_contra h
      have ho : n < -2 ∨ 0 < n := by omega
      exact (not_subsingleton_iff_nontrivial.mpr hn) (L.outside Q z n ho)
    let i : Fin 3 := ⟨(n + 2).toNat, by omega⟩
    have he : ordinaryDegree i = n := by simp only [ordinaryDegree, i]; omega
    refine ⟨i, ?_⟩
    change Module.finrank E (pointCohomology D point hPoint fiber Q z (ordinaryDegree i)) ≠ 0
    rw [he]
    let := L.finite Q z n
    exact (Module.finrank_pos_iff.mpr hn).ne'

variable (D point hPoint fiber)

/-- Only the remaining general geometric observables; dimensions and
support are not selectable fields. -/
structure RemainingObservables where
  constituents : Obj D → List (Obj D)
  Pure : Obj D → Prop
  Simple : Obj D → Prop
  complexity : Obj D → ℕ

variable (O : RemainingObservables D)

def surfaceData : SurfaceData k (Obj D) where
  geomDim := geometricDimension D point hPoint fiber
  support := geometricSupport D point hPoint fiber
  constituents := O.constituents
  Pure := O.Pure
  Simple := O.Simple
  complexity := O.complexity

theorem minusTwo_dimension (Q : Obj D) (z : k × k) :
    (surfaceData D point hPoint fiber O).geomDim Q z 0 =
      Module.finrank E (pointCohomology D point hPoint fiber Q z (-2)) := rfl

theorem minusOne_dimension (Q : Obj D) (z : k × k) :
    (surfaceData D point hPoint fiber O).geomDim Q z 1 =
      Module.finrank E (pointCohomology D point hPoint fiber Q z (-1)) := rfl

theorem zero_dimension (Q : Obj D) (z : k × k) :
    (surfaceData D point hPoint fiber O).geomDim Q z 2 =
      Module.finrank E (pointCohomology D point hPoint fiber Q z 0) := rfl

theorem support_eq_ordinary_union (Q : Obj D) :
    (surfaceData D point hPoint fiber O).support Q =
      ⋃ i : Fin 3, (surfaceData D point hPoint fiber O).ordinarySupport Q i := by
  ext z
  simp only [surfaceData, geometricSupport, SurfaceData.ordinarySupport,
    Set.mem_ofPred_eq, Set.mem_iUnion]

/-- The actual native point functor makes dimensions invariant under
native perverse isomorphism, in every ordinary degree. -/
theorem geometricDimension_iso {Q R : Obj D} (e : Q ≅ R) (z : k × k) (i : Fin 3) :
    geometricDimension D point hPoint fiber Q z i =
      geometricDimension D point hPoint fiber R z i :=
  ((pointCohomologyFunctor D point hPoint fiber z (ordinaryDegree i)).mapIso e).toLinearEquiv.finrank_eq

/-- Same nonzero-stalk support under the actual native isomorphism. -/
theorem geometricSupport_iso {Q R : Obj D} (e : Q ≅ R) :
    geometricSupport D point hPoint fiber Q = geometricSupport D point hPoint fiber R := by
  ext z
  simp only [geometricSupport, Set.mem_ofPred_eq]
  apply exists_congr
  intro i
  rw [geometricDimension_iso D point hPoint fiber e z i]

end PrimeGap182.TypeIII.NativeSurfaceFromGeometricStalks

#print axioms PrimeGap182.TypeIII.NativeSurfaceFromGeometricStalks.point_linearMorphism
#print axioms PrimeGap182.TypeIII.NativeSurfaceFromGeometricStalks.surfaceData
#print axioms PrimeGap182.TypeIII.NativeSurfaceFromGeometricStalks.geometricDimension_iso
#print axioms PrimeGap182.TypeIII.NativeSurfaceFromGeometricStalks.geometricSupport_iso
