import TypeIIIPureDualTrace
import TypeIIISharedCohomology

/-!
# Exact stalks and purity of the original cohomological image

The canonical image comparison intertwines the original natural Frobenius.
The general guarded cohomological-image weight theorem and the pointwise
definition of purity remain explicit inputs. In particular the relative
weight input includes the applicable cohomology/base-change interpretation;
unrestricted ordinary base change is not inferred from compact base change.
Weil II 3.3.6 and 3.3.10 give the fiber pure-image theorem, and 1.2.6 gives
the fixed-embedding pointwise weight convention.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PrimeGap182.TypeIII.PointImagePurity
open SourceInverseImageSystem RationalPointStalks PublishedPhysicalConstruction

universe u v w mu h

section Image
variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ ModuleCat.{w} ℂ) (Fr : F ⟶ F) {A B : C} (f : A ⟶ B)

/-- Image of the original Frobenius square, with no new endomorphism choice. -/
def imageFrobenius : Abelian.image (F.map f) ⟶ Abelian.image (F.map f) :=
  Abelian.im.map (Arrow.homMk (f := Arrow.mk (F.map f)) (g := Arrow.mk (F.map f))
    (Fr.app A) (Fr.app B) (Fr.naturality f).symm)

omit [Abelian C] in
theorem imageFrobenius_inclusion :
    imageFrobenius F Fr f ≫ Abelian.image.ι (F.map f) =
      Abelian.image.ι (F.map f) ≫ Fr.app B := by
  change kernel.lift _ _ _ ≫ kernel.ι _ = _
  exact kernel.lift_ι _ _ _

omit [Abelian C] in
theorem projection_imageFrobenius :
    Abelian.factorThruImage (F.map f) ≫ imageFrobenius F Fr f =
      Fr.app A ≫ Abelian.factorThruImage (F.map f) := by
  apply (cancel_mono (Abelian.image.ι (F.map f))).mp
  rw [Category.assoc, imageFrobenius_inclusion, ← Category.assoc,
    Abelian.image.fac, Category.assoc, Abelian.image.fac]
  exact Fr.naturality f

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exactness compares images using their original inclusion and quotient;
naturality then proves compatibility with the original stalk Frobenius. -/
theorem imageIso_frobenius :
    (Abelian.PreservesImage.iso F f).hom ≫ imageFrobenius F Fr f =
      Fr.app (Abelian.image f) ≫ (Abelian.PreservesImage.iso F f).hom := by
  apply (cancel_mono (Abelian.image.ι (F.map f))).mp
  rw [Category.assoc, imageFrobenius_inclusion, ← Category.assoc,
    Abelian.PreservesImage.iso_hom_ι, Category.assoc, Abelian.PreservesImage.iso_hom_ι]
  exact Fr.naturality (Abelian.image.ι f)

/-- Conjugacy preserves the entire characteristic polynomial, including
algebraic multiplicities; it requires no semisimplicity assumption. -/
theorem imageIso_charpoly [FiniteDimensional ℂ (F.obj (Abelian.image f))]
    [FiniteDimensional ℂ (Abelian.image (F.map f) : ModuleCat.{w} ℂ)] :
    LinearMap.charpoly (Fr.app (Abelian.image f)).hom =
      LinearMap.charpoly (imageFrobenius F Fr f).hom := by
  let e := (Abelian.PreservesImage.iso F f).toLinearEquiv
  have hn (v) : e ((Fr.app (Abelian.image f)).hom v) =
      (imageFrobenius F Fr f).hom (e v) :=
    (congrArg (fun m => m.hom v) (imageIso_frobenius F Fr f)).symm
  have hc : e.conj (Fr.app (Abelian.image f)).hom =
      (imageFrobenius F Fr f).hom := by
    ext v
    change e ((Fr.app (Abelian.image f)).hom (e.symm v)) = _
    rw [hn, e.apply_symm_apply]
  exact (LinearEquiv.charpoly_conj e _).symm.trans (congrArg LinearMap.charpoly hc)

end Image

variable {p : ℕ} [Fact p.Prime] {B : System.{0,mu} (ZMod p)} (R : Data B)

/-- Common exactness of rational-point stalks on all background spaces. -/
structure ExactStalks : Prop where
  additive : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x,
    (R.fiber E X x).Additive
  limits : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x,
    PreservesFiniteLimits (R.fiber E X x)
  colimits : ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E] X x,
    PreservesFiniteColimits (R.fiber E X x)

/-- Converse direction of fixed-embedding pointwise purity. Every actual
rational scheme point over every finite extension is quantified. -/
structure PurityReflection (X : Space (ZMod p)) (Pure : B.Obj X → ℝ → Prop) : Prop where
  pure : ∀ A w, (∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (x : Spec (.of E) ⟶ scheme (ZMod p) X), ∀ z ∈ PureDualTrace.eigenvalues R E X x A,
      Complex.normSq z = (Fintype.card E : ℝ) ^ w) → Pure A w

/-- Characteristic roots of the literal linear image of the original map. -/
def imageEigenvalues (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X)
    {A C : B.Obj X} (f : A ⟶ C) : Multiset ℂ := by
  letI := R.finite E X x C
  letI := FiniteDimensional.of_injective (Abelian.image.ι ((R.fiber E X x).map f)).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact (LinearMap.charpoly (imageFrobenius (R.fiber E X x) (R.frobenius E X x) f).hom).roots

theorem image_eigenvalues (S : ExactStalks R)
    (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (X : Space (ZMod p)) (x : Spec (.of E) ⟶ scheme (ZMod p) X)
    {A C : B.Obj X} (f : A ⟶ C) :
    PureDualTrace.eigenvalues R E X x (Abelian.image f) = imageEigenvalues R E X x f := by
  let := S.additive E X x
  let := S.limits E X x
  let := S.colimits E X x
  let := R.finite E X x C
  let := R.finite E X x (Abelian.image f)
  let := FiniteDimensional.of_injective (Abelian.image.ι ((R.fiber E X x).map f)).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact congrArg Polynomial.roots (imageIso_charpoly (R.fiber E X x) (R.frobenius E X x) f)

variable {Point : Type h} (D : CurveData (B.Obj .source) Point)
  (H : CohomologyData (B.Obj .source) (B.Obj .torus)) (P : ParameterData (B.Obj .torus))

/-- General guarded relative application of the pure-image theorem to the
literal mapped comparison. Fiber identification and its range of validity
remain part of this explicit published input, not a proved base-change law. -/
structure ImageWeights : Prop where
  weight : ∀ A a, D.Lisse A → D.Pure A a →
    D.Isoclinic A 1 → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact A) → P.Lisse (H.compact (D.dual A)) →
    ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
      (x : Spec (.of E) ⟶ scheme (ZMod p) .torus),
      ∀ z ∈ imageEigenvalues R E .torus x (H.comparison A),
        Complex.normSq z = (Fintype.card E : ℝ) ^ (a + 1)

/-- The six other physical laws, with no purity assertion about the image. -/
structure OtherRules : Prop where
  dualTate_lisse : ∀ A, P.Lisse A → P.Lisse (P.dualTateMinusOne A)
  lisse_of_iso : ∀ A B, Nonempty (A ≅ B) → P.Lisse B → P.Lisse A
  image_lisse : ∀ A B (f : A ⟶ B), P.Lisse A → P.Lisse B → P.Lisse (Abelian.image f)
  signed_lisse : ∀ A, P.Lisse A → P.Lisse (P.signed A)
  signed_pure : ∀ A a, P.Pure A a → P.Pure (P.signed A) a
  dualTate_pure : ∀ A a, P.Lisse A → P.Pure A a → P.Pure (P.dualTateMinusOne A) (2 - a)

variable {R D H P}

/-- Apply weights through the proved original-Frobenius image comparison,
and then the definition of purity. All original geometric guards remain. -/
theorem image_pure (S : ExactStalks R) (W : ImageWeights R D H P)
    (T : PurityReflection R .torus P.Pure) (A : B.Obj .source) (a : ℝ)
    (hl : D.Lisse A) (hp : D.Pure A a) (hs : D.Isoclinic A 1)
    (hd : D.Isoclinic (D.dual A) 1) (hc : P.Lisse (H.compact A))
    (hcd : P.Lisse (H.compact (D.dual A))) : P.Pure (parabolicCore H A) (a + 1) := by
  apply T.pure
  intro E _ _ _ x z hz
  rw [show parabolicCore H A = Abelian.image (H.comparison A) from rfl,
    image_eigenvalues R S] at hz
  exact W.weight A a hl hp hs hd hc hcd E x z hz

theorem physicalRules (S : ExactStalks R) (W : ImageWeights R D H P)
    (T : PurityReflection R .torus P.Pure) (G : OtherRules P) :
    SharedCohomology.OtherRules D H P where
  dualTate_lisse := G.dualTate_lisse
  lisse_of_iso := G.lisse_of_iso
  image_lisse := G.image_lisse
  image_pure := image_pure S W T
  signed_lisse := G.signed_lisse
  signed_pure := G.signed_pure
  dualTate_pure := G.dualTate_pure

end PrimeGap182.TypeIII.PointImagePurity

#print axioms PrimeGap182.TypeIII.PointImagePurity.imageFrobenius
#print axioms PrimeGap182.TypeIII.PointImagePurity.imageFrobenius_inclusion
#print axioms PrimeGap182.TypeIII.PointImagePurity.projection_imageFrobenius
#print axioms PrimeGap182.TypeIII.PointImagePurity.imageIso_frobenius
#print axioms PrimeGap182.TypeIII.PointImagePurity.imageIso_charpoly
#print axioms PrimeGap182.TypeIII.PointImagePurity.imageEigenvalues
#print axioms PrimeGap182.TypeIII.PointImagePurity.image_eigenvalues
#print axioms PrimeGap182.TypeIII.PointImagePurity.image_pure
#print axioms PrimeGap182.TypeIII.PointImagePurity.physicalRules
