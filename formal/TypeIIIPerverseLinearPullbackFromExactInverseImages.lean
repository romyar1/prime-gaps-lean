import TypeIIIOriginPoleFromExactInverseImages
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Native perverse linear pullback and radial realization

The curve and full-plane objects are admissible full subcategories of the
SAME native standard derived categories used by the common ordinary
extension. Their bounded-constructible, perverse interpretation remains
general model data. The only geometric closure law is smooth inverse
image with the relative-dimension-one [1] shift, for EVERY nonzero linear
map A2_k -> A1_k (BBD 4.2.5; also Laumon 1.3.2.3, proof).

Fourier, inverse, profile and phases remain operations on these SAME
plane objects. The linear pullback is constructed from actual native
inverse image followed by [1]. The zero direction, outside the smooth
theorem's domain, is defined to be a zero object. Both affine origins
and the full source plane are retained. Radial inertia is defined by the
actual radial inverse image, ordinary H^-2 and the SAME ordinary wild
functor as the original AS pole realization. Thus the former specific
linearRealization and radialStalk isomorphisms become identities.

For an intended continuous constructible Q2-adic model, p != 2 and the
identification of the admissible native objects with the bounded perverse
heart are still explicit realization scope. This does not construct the
Fourier transform, its published laws, or a complete common input family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Classical ZeroObject

namespace PrimeGap182.TypeIII.PerverseLinearPullbackFromExactInverseImages

open PublishedFourierRules ExactInverseImagesToDerived
open LinearRadialPhaseFromPoleTransport OriginPoleFromExactInverseImages

universe w e g

variable {K0 k J : Type} [Field K0] [Field k]
  {B : SourceInverseImageSystem.System.{0,w} K0}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{w} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{w} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{w} (OC i)] [∀ i, Abelian (OC i)]
  (A : OrdinarySystem (extensionScheme (extraScheme k otherScheme))
    (extensionObjects B (extraObjects NC LC OC)))

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{w} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

/-- The actual admissible native perverse objects. Their geometric
interpretation, including bounded constructibility, remains external. -/
structure Admissibility where
  curve : ObjectProperty ((nativeSystem A).Derived .curve)
  plane : ObjectProperty ((nativeSystem A).Derived .plane)
  [curveIso : curve.IsClosedUnderIsomorphisms]
  [planeIso : plane.IsClosedUnderIsomorphisms]
  [planeZero : plane.ContainsZero]

attribute [instance] Admissibility.curveIso Admissibility.planeIso Admissibility.planeZero

variable {A} (D : Admissibility A)

abbrev CurveObj := D.curve.FullSubcategory

abbrev Obj := D.plane.FullSubcategory

/-- General BBD smooth [1] perverse closure, universally before selecting
any Type-III objects. The zero linear direction is explicitly excluded. -/
structure SmoothPullbackLaw : Prop where
  smooth : ∀ Q a b, (a, b) ≠ (0, 0) → D.curve Q →
    D.plane (((nativeSystem A).shiftOne .plane).obj
      (((nativeSystem A).derivedPull (i := .plane) (j := .curve)
        (linearMorphism a b)).obj Q))

variable {D} (L : SmoothPullbackLaw D)

/-- The nonzero-direction functor is the actual native inverse image [1]
lifted to the admissible full subcategory. -/
def linearPullbackFunctor (a b : k) (hab : (a, b) ≠ (0, 0)) :
    CurveObj D ⥤ Obj D :=
  D.plane.lift (D.curve.ι ⋙
    (nativeSystem A).derivedPull (i := .plane) (j := .curve) (linearMorphism a b) ⋙
    (nativeSystem A).shiftOne .plane)
    (fun Q => L.smooth Q.obj a b hab Q.property)

/-- The entire inclusion comparison is an identity on native functors. -/
def linearPullbackRealization (a b : k) (hab : (a, b) ≠ (0, 0)) :
    linearPullbackFunctor L a b hab ⋙ D.plane.ι ≅
      D.curve.ι ⋙
        (nativeSystem A).derivedPull (i := .plane) (j := .curve) (linearMorphism a b) ⋙
        (nativeSystem A).shiftOne .plane := Iso.refl _

/-- Only the four remaining operations/observables on these fixed native
plane objects; no linear pullback or origin comparison is a field. -/
structure Operations (D : Admissibility A) where
  fourier : Obj D → Obj D
  inverse : Obj D → Obj D
  HasSimpleRadialPhases : Obj D → Prop
  phases : Obj D → Set (LinearRadialPhaseFromPoleTransport.L k)

variable (P : Operations D)

/-- Totality at the zero direction uses a zero perverse object, not a
smooth-pullback assertion about the constant map. -/
def linearPullback (v : k × k) (Q : CurveObj D) : Obj D :=
  if h : v ≠ (0, 0) then (linearPullbackFunctor L v.1 v.2 h).obj Q else 0

def fourierData : FourierData k (Obj D) (CurveObj D) where
  fourier := P.fourier
  inverse := P.inverse
  linearPullback := linearPullback L
  HasSimpleRadialPhases := P.HasSimpleRadialPhases
  phases := P.phases

variable {E : Type e} [Field E] {G : Type g} [Group G]
  (W : OrdinaryWild (E := E) (G := G) A)

/-- Ordinary H^-2 after the actual radial inverse image, then the SAME
origin wild functor (punctured inverse image followed by W.wildLocal). -/
def radialFunctor : Obj D ⥤ FDRep E G :=
  D.plane.ι ⋙
    (nativeSystem A).derivedPull (i := .origin) (j := .plane) (radialMorphism (k := k)) ⋙
    (nativeSystem A).ordinary .origin (-2) ⋙ W.originWild

def radial : Obj D → FDRep E G := (radialFunctor (D := D) W).obj

/-- The four old original-object fields are constructed; both formerly
specific comparison isomorphisms are identities by definition. -/
def originalObjects : OriginalObjects W (fourierData L P) (radial (D := D) W) where
  curveRealization Q := Q.obj
  planeRealization Q := Q.obj
  linearRealization Q a b hab := by
    change (linearPullback L (a, b) Q).obj ≅ _
    simp only [linearPullback, dite_eq_left hab]
    exact Iso.refl _
  radialStalk _Q := Iso.refl _

end PrimeGap182.TypeIII.PerverseLinearPullbackFromExactInverseImages

#print axioms PrimeGap182.TypeIII.PerverseLinearPullbackFromExactInverseImages.linearPullbackRealization
#print axioms PrimeGap182.TypeIII.PerverseLinearPullbackFromExactInverseImages.fourierData
#print axioms PrimeGap182.TypeIII.PerverseLinearPullbackFromExactInverseImages.radialFunctor
#print axioms PrimeGap182.TypeIII.PerverseLinearPullbackFromExactInverseImages.originalObjects
