import TypeIIIRankTwoFourierKernelCoordinates
import TypeIIINativeTheoryFromRadialPhaseData
import TypeIIIPublishedPrimitiveSources

/-!
# Rank-two Fourier from the full native AS pairing kernel

The extra kernel index is the ACTUAL full A4 over Fpbar, in the SAME
original-B-preserving ordinary inverse-image extension as the native
perverse A2. Both projections and the positive pairing x0*xi0+x1*xi1
are actual Spec maps. The AS operation is the ORIGINAL prime-field
operation, pulled along the pairing and canonical base-field map, then
embedded in degree0. No kernel or Fourier operation is freely selected.

General derived tensor, indexed compact pushforward and Tate functors
remain framework data on these fixed native categories. The transform
is their full AS kernel composite with the actual positive [2] shift.
Its inverse is the SAME dual transform followed by actual reflection
pullback and Tate(+2). Published laws quantify over EVERY nontrivial
two-adic additive character and EVERY fixed native bounded-perverse
object: Laumon1.3.2.3 (perverse exactness) and1.2.2.3 (quasi-inverse).
They are restricted to that domain, not all unbounded native complexes.
The canonical application discharges character nontriviality.

This is a conditional published-theorem application, not an adic
foundational reconstruction. Native bounded-constructible/perverse and
continuous Q2-adic interpretation, p!=2, the usual derived tensor,
compact-push and Tate realization, and original AS realization remain
explicit. No complete common Inputs or Fourier-support law is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped Classical PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel

open ExactInverseImagesToDerived OriginPoleFromExactInverseImages
open PerverseLinearPullbackFromExactInverseImages LinearRadialPhaseFromPoleTransport

universe mu e g

variable {p : ℕ} [Fact p.Prime] {J : Type}
  {B : SourceInverseImageSystem.System.{0,mu} (ZMod p)}
  {otherScheme : J → Scheme}
  {NC : OriginRealizationFromExactInverseImages.Index → Type}
  [∀ i, Category.{mu} (NC i)] [∀ i, Abelian (NC i)]
  {LC : Type} [Category.{mu} LC] [Abelian LC]
  {OC : J → Type} [∀ i, Category.{mu} (OC i)] [∀ i, Abelian (OC i)]
  {A : OrdinarySystem (extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme))
    (extensionObjects B (extraObjects NC LC OC))}
  (kernel : J)
  (hKernel : otherScheme kernel =
    RankTwoFourierKernelCoordinates.kernelScheme (AlgebraicClosure (ZMod p)))

def kernelIndex (i : J) : CommonIndex (K0 := ZMod p) (J := J) :=
  Sum.inr (Sum.inr (Sum.inr i))

local instance commonLocalizations : ∀ i, HasDerivedCategory.{mu}
    (extensionObjects B (extraObjects NC LC OC) i) :=
  fun i => HasDerivedCategory.standard (extensionObjects B (extraObjects NC LC OC) i)

local instance nativeLocalizations : ∀ i, HasDerivedCategory.{mu} (NC i) :=
  fun i => HasDerivedCategory.standard (NC i)

abbrev KernelDerived := A.Derived (kernelIndex (p := p) kernel)

variable [MonoidalCategory (KernelDerived (A := A) kernel)]

/-- Actual source projection from the chosen full A4 index. -/
def sourceMap :
    extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme)
      (kernelIndex (p := p) kernel) ⟶
    OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) .plane :=
  eqToHom hKernel ≫ RankTwoFourierKernelCoordinates.sourceMorphism (AlgebraicClosure (ZMod p))

/-- Actual target projection, retaining the entire target A2 including0. -/
def targetMap :
    extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme)
      (kernelIndex (p := p) kernel) ⟶
    OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) .plane :=
  eqToHom hKernel ≫ RankTwoFourierKernelCoordinates.targetMorphism (AlgebraicClosure (ZMod p))

/-- Positive dot product followed by the ORIGINAL base-field map to the
original B source-line scheme. -/
def phaseMap :
    extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme)
      (kernelIndex (p := p) kernel) ⟶
    SourceInverseImageSystem.scheme (ZMod p) .line :=
  eqToHom hKernel ≫ RankTwoFourierKernelCoordinates.pairingMorphism (AlgebraicClosure (ZMod p)) ≫
    baseLineMorphism (ZMod p) (AlgebraicClosure (ZMod p))

/-- Only general tensor/compact/Tate framework on fixed native categories.
The compact functor is indexed by ALL actual A4-to-A2 maps. -/
structure Data where
  compactPush : ∀ (_f :
    extensionScheme (extraScheme (AlgebraicClosure (ZMod p)) otherScheme)
      (kernelIndex (p := p) kernel) ⟶
    OriginRealizationFromExactInverseImages.scheme (AlgebraicClosure (ZMod p)) .plane),
    KernelDerived (A := A) kernel ⥤ (nativeSystem A).Derived .plane
  tate : ℤ → (nativeSystem A).Derived .plane ⥤ (nativeSystem A).Derived .plane

variable (F : Data (A := A) kernel)
  (AS : AddChar (ZMod p) (PadicAlgCl 2) → B.Obj .line)

/-- The original ordinary AS operation pulled along the full pairing. -/
def ordinaryAS (ψ : AddChar (ZMod p) (PadicAlgCl 2)) : OC kernel :=
  (A.pull (i := kernelIndex kernel) (j := sourceIndex) (phaseMap kernel hKernel)).obj (AS ψ)

/-- Degree0 embedding of that SAME original AS pullback. -/
def fullAS (ψ : AddChar (ZMod p) (PadicAlgCl 2)) : KernelDerived (A := A) kernel :=
  (A.degreeZero (kernelIndex kernel)).obj (ordinaryAS (A := A) kernel hKernel AS ψ)

/-- Native exact inverse image gives the original derived AS pullback
comparison; no sheaf kernel comparison is assumed. -/
def fullASPullback (ψ : AddChar (ZMod p) (PadicAlgCl 2)) :
    (A.derivedPull (i := kernelIndex kernel) (j := sourceIndex) (phaseMap kernel hKernel)).obj
      ((A.degreeZero sourceIndex).obj (AS ψ)) ≅ fullAS (A := A) kernel hKernel AS ψ :=
  (A.degreeZeroPullback (i := kernelIndex kernel) (j := sourceIndex)
    (phaseMap kernel hKernel)).app (AS ψ)

/-- The actual full A4 AS pairing kernel followed by compact push and [2]. -/
def Data.derivedTransform (ψ : AddChar (ZMod p) (PadicAlgCl 2)) :
    (nativeSystem A).Derived .plane ⥤ (nativeSystem A).Derived .plane :=
  A.derivedPull (i := kernelIndex kernel) (j := nativeIndex .plane) (sourceMap kernel hKernel) ⋙
    tensorRight (fullAS (A := A) kernel hKernel AS ψ) ⋙ F.compactPush (targetMap kernel hKernel) ⋙
    shiftFunctor ((nativeSystem A).Derived .plane) (2 : ℤ)

/-- Actual reflection inverse image on the SAME full native A2. -/
def reflectionPull : (nativeSystem A).Derived .plane ⥤ (nativeSystem A).Derived .plane :=
  (nativeSystem A).derivedPull (i := .plane) (j := .plane)
    (RankTwoFourierKernelCoordinates.reflectionMorphism (AlgebraicClosure (ZMod p)))

/-- Laumon's quasi-inverse: same dual Fourier transform, reflection, Tate(+2). -/
def Data.derivedInverse (ψ : AddChar (ZMod p) (PadicAlgCl 2)) :
    (nativeSystem A).Derived .plane ⥤ (nativeSystem A).Derived .plane :=
  F.derivedTransform kernel hKernel AS ψ ⋙ reflectionPull (A := A) ⋙ F.tate (2 : ℤ)

/-- Numerical/adic scope is explicit. ALL character-indexed laws below
are universal on the native bounded-perverse domain, before any family
selection. The two comparisons are the general quasi-inverse theorem
applied to the computed full pairing transform, not an arbitrary Fourier. -/
structure PublishedLaws (D : Admissibility A) (_hp2 : p ≠ 2) where
  perverseExact : ∀ ψ, ψ ≠ 1 → ∀ P, D.plane P →
    D.plane ((F.derivedTransform kernel hKernel AS ψ).obj P)
  isomorphismPerverse : ∀ e :
    RankTwoFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)) ≅
      RankTwoFourierKernelCoordinates.planeScheme (AlgebraicClosure (ZMod p)),
    ∀ P, D.plane P → D.plane (((nativeSystem A).derivedPull (i := .plane) (j := .plane) e.hom).obj P)
  tatePerverse : ∀ n P, D.plane P → D.plane ((F.tate n).obj P)
  unitComparison : ∀ ψ, ψ ≠ 1 →
    (D.plane.ι ⋙ (F.derivedTransform kernel hKernel AS ψ ⋙ F.derivedInverse kernel hKernel AS ψ) ≅
      D.plane.ι)
  counitComparison : ∀ ψ, ψ ≠ 1 →
    (D.plane.ι ⋙ (F.derivedInverse kernel hKernel AS ψ ⋙ F.derivedTransform kernel hKernel AS ψ) ≅
      D.plane.ι)

variable {kernel hKernel F AS} {D : Admissibility A} {hp2 : p ≠ 2}
  (L : PublishedLaws kernel hKernel F AS D hp2)

/-- The canonical nontriviality theorem discharges the published guard. -/
def fourierFunctor : Obj D ⥤ Obj D :=
  D.plane.lift (D.plane.ι ⋙ F.derivedTransform kernel hKernel AS (CanonicalSourceCharacter.prime p))
    (fun P => L.perverseExact _ (CanonicalSourceCharacter.prime_ne_one p) P.obj P.property)

def inverseFunctor : Obj D ⥤ Obj D :=
  D.plane.lift (D.plane.ι ⋙ F.derivedInverse kernel hKernel AS (CanonicalSourceCharacter.prime p))
    (fun P => L.tatePerverse (2 : ℤ) _
      (L.isomorphismPerverse (RankTwoFourierKernelCoordinates.reflectionIso (AlgebraicClosure (ZMod p))) _
        (L.perverseExact _ (CanonicalSourceCharacter.prime_ne_one p) P.obj P.property)))

/-- Entire native Fourier realization is an identity of actual functors. -/
def fourierRealization : fourierFunctor L ⋙ D.plane.ι ≅
    D.plane.ι ⋙ F.derivedTransform kernel hKernel AS (CanonicalSourceCharacter.prime p) := Iso.refl _

def inverseRealization : inverseFunctor L ⋙ D.plane.ι ≅
    D.plane.ι ⋙ F.derivedInverse kernel hKernel AS (CanonicalSourceCharacter.prime p) := Iso.refl _

/-- Lift the published natural comparisons through the actual full
subcategory inclusion; equivariance/coherence are not objectwise choices. -/
def unitIso : 𝟭 (Obj D) ≅ fourierFunctor L ⋙ inverseFunctor L :=
  NatIso.ofComponents (fun P => D.plane.isoMk
    ((L.unitComparison _ (CanonicalSourceCharacter.prime_ne_one p)).app P).symm)
    (by intro P Q f; apply ObjectProperty.hom_ext; exact
      (L.unitComparison _ (CanonicalSourceCharacter.prime_ne_one p)).inv.naturality f)

def counitIso : inverseFunctor L ⋙ fourierFunctor L ≅ 𝟭 (Obj D) :=
  NatIso.ofComponents (fun P => D.plane.isoMk
    ((L.counitComparison _ (CanonicalSourceCharacter.prime_ne_one p)).app P))
    (by intro P Q f; apply ObjectProperty.hom_ext; exact
      (L.counitComparison _ (CanonicalSourceCharacter.prime_ne_one p)).hom.naturality f)

/-- Genuine perverse equivalence retaining the actual full-kernel forward
and reflection/Tate inverse functors. -/
def perverseEquivalence : Obj D ≌ Obj D :=
  CategoryTheory.Equivalence.mk (fourierFunctor L) (inverseFunctor L) (unitIso L) (counitIso L)

variable {E : Type e} [Field E] {G : Type g} [Group G]
  (W : OrdinaryWild (E := E) (G := G) A)
  (PD : PublishedPhaseApplication.PhaseData (AlgebraicClosure (ZMod p)) E G)

/-- Native Fourier/inverse are constructed, while radial observables use
the SAME native H^-2/W and PD as the checked global theory constructor. -/
def operations : Operations D :=
  NativeTheoryFromRadialPhaseData.operations D (fourierFunctor L).obj (inverseFunctor L).obj W PD

end PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel

#print axioms PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel.fullASPullback
#print axioms PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel.Data.derivedTransform
#print axioms PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel.fourierRealization
#print axioms PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel.unitIso
#print axioms PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel.perverseEquivalence
#print axioms PrimeGap182.TypeIII.RankTwoFourierFromNativeASKernel.operations
