import TypeIIISourceProjectionForQST
import TypeIIIIntermediateExtensionFromImage
import TypeIIIPublishedConstructionComplexity
import TypeIIIStartingSourceComplexity

/-!
# Both original complexity records from one common QST realization

The theorem parameters here are general QST operations on arbitrary
geometric objects and maps, ordinary cohomology, perverse images, open
intermediate extensions, and the two published primitive classes. They do
not contain the thirteen inequalities in the original QB/QS records.

The index fixes the actual affine presentations whose STANDARD projective
completions are P1, P1, P6, P4, P2 and P2. The torus has two embedding indices:
the existing A4 closed presentation and the actual open in A2. The map
between those two indices is the identity of the SAME torus scheme.

No adic category or standard projective-chart foundation is constructed.
`GeometricModel` is the explicit common published background; its semantic
identification with those standard completions remains required. The
common realization supplies operation isomorphisms and observable/class
identifications, including the SAME source projection, sign line, dual
objects, and original perverse support arrow. It supplies no bound on a
finished input or IC family and takes no whole root Inputs premise.

All envelope constants have a type WITHOUT p. The caller must fix one
`UniformConstants` before selecting a characteristic, and verify the same
fixed-presentation caps for each realization. The resulting function is a
generated finite monotone envelope, or is dominated by the old boundFn.

Primary reference: Sawin--Forey--Fresan--Kowalski, QST v4,
https://arxiv.org/html/2101.00635v4 : 6.8(4),(5),(8),(9), 6.14(3),
6.15, 6.16, 6.19, 6.24, 7.5(1), 7.8(1). These are explicit theorem
parameters, not proofs or independently checked citation matches here.
6.24 and 7.5/7.8 are Propositions; 6.16 is a Corollary. Twist equality
means geometric Tate invariance, not a printed 6.14 assertion. The
ordinary-middle-extension law is the general one-boundary-point
rank/triangle corollary. In particular 7.8 is applied on Gm, not silently
asserted on every object of the original affine-line class.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Classical MonoidalCategory ZeroObject

namespace PrimeGap182.TypeIII.UniformComplexityFromCommonRealization
open PublishedPhysicalConstruction PublishedPolynomialComplexity
open PublishedConstructionComplexity StartingSourceComplexity StartingSourceMaps
open SourceInverseImageSystem

inductive Space where
  | gm | line | source | torus4 | torus2 | plane
  deriving DecidableEq, Fintype

def ambientDimension : Space → ℕ
  | .gm | .line => 1 | .source => 6 | .torus4 => 4 | .torus2 => 2 | .plane => 2

variable (K : Type) [Field K]

abbrev affinePlane : Scheme := Spec (.of (MvPolynomial (Fin 2) K))

/-- The actual open map, using the original two torus coordinate units. -/
def torusOpen : PhysicalTorusMorphism.torusScheme K ⟶ affinePlane K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval ![(PhysicalTorusMorphism.xUnit K : PhysicalTorusMorphism.TorusRing K),
      (PhysicalTorusMorphism.yUnit K : PhysicalTorusMorphism.TorusRing K)]).toRingHom)

def scheme : Space → Scheme
  | .gm => ArithmeticSourceMaps.fiberScheme K
  | .line => affineLine K
  | .source => sourceScheme K
  | .torus4 | .torus2 => PhysicalTorusMorphism.torusScheme K
  | .plane => affinePlane K

/-- Literal affine presentations; the QST background uses their standard
projective completions. This definition does not replace P4 by P2. -/
def affineEmbedding (i : Space) : scheme K i ⟶
    Spec (.of (MvPolynomial (Fin (ambientDimension i)) K)) := by
  cases i with
  | gm => exact ArithmeticSourceMaps.localInputMorphism K K
  | line => exact 𝟙 _
  | source => exact sourceEmbedding K
  | torus4 => exact PhysicalTorusLaurent.torusAffineEmbedding K
  | torus2 => exact torusOpen K
  | plane => exact 𝟙 _

/-- Constants for general operations depend on embedding DIMENSIONS.
Caps concern the fixed presentations and are fixed BEFORE p. N bounds
ordinary cohomology and is not presumed monotone. -/
structure UniformConstants where
  dual : ℕ → ℕ
  tensor : ℕ → ℕ
  pull : ℕ → ℕ → ℕ
  push : ℕ → ℕ → ℕ
  image : ℕ → ℕ
  ic : ℕ → ℕ
  ordinary : ℕ → ℕ → ℕ
  E6 : ℕ
  E4 : ℕ
  E2 : ℕ
  Ew : ℕ
  projection : ℕ
  changeEmbedding : ℕ
  hypergeometric : ℕ

universe g gh h hh

/-- One geometric framework, after geometric coefficient/base realization.
Operations and map complexity quantify over arbitrary objects and actual
scheme maps, rather than the selected Type III input term. `Induced` means
the source embedding is induced by the target embedding and open map.
Its standard-projective semantic realization remains a background duty. -/
structure GeometricModel where
  Obj : Space → Type g
  [category : ∀ i, Category.{gh} (Obj i)]
  [zeroObject : ∀ i, HasZeroObject (Obj i)]
  complexity : ∀ i, Obj i → ℕ
  /-- Ordinary degree-zero rank-one objects geometrically isomorphic
  to the unit after the SAME coefficient/base realization. -/
  GeometricConstantRankOne : ∀ i, Obj i → Prop
  embeddingComplexity : Space → ℕ
  mapComplexity : ∀ {i j}, (scheme K i ⟶ scheme K j) → ℕ
  tensor : ∀ i, Obj i → Obj i → Obj i
  unit : ∀ i, Obj i
  tensorIso : ∀ i {A A' B B' : Obj i}, (A ≅ A') → (B ≅ B') →
    (tensor i A B ≅ tensor i A' B')
  tensorUnit : ∀ i A, tensor i (unit i) A ≅ A
  shift : ∀ i, Obj i → ℤ → Obj i
  twist : ∀ i, Obj i → ℤ → Obj i
  verdier : ∀ i, Obj i → Obj i
  ordinary : ∀ i, Obj i → ℤ → Obj i
  pull : ∀ {i j}, (scheme K i ⟶ scheme K j) → Obj j → Obj i
  push : ∀ {i j}, (scheme K i ⟶ scheme K j) → Obj i → Obj j
  Perv : Space → Type h
  [perverseCategory : ∀ i, Category.{hh} (Perv i)]
  [perverseAbelian : ∀ i, Abelian (Perv i)]
  perverse : ∀ i, Perv i ⥤ Obj i
  openZero : ∀ {i j}, (scheme K i ⟶ scheme K j) → Perv i ⥤ Perv j
  openDirect : ∀ {i j}, (scheme K i ⟶ scheme K j) → Perv i ⥤ Perv j
  openSupport : ∀ {i j} (f : scheme K i ⟶ scheme K j), openZero f ⟶ openDirect f
  Induced : ∀ {i j}, (scheme K i ⟶ scheme K j) → Prop
  /-- Ordinary H0 geometric GENERIC stalk after the common coefficient
  realization. This is not a point selected at the possible singularity 1. -/
  gmGenericFiber : Obj .gm → ModuleCat.{0} ℂ
  [gmGenericFinite : ∀ A, FiniteDimensional ℂ (gmGenericFiber A)]
  /-- Ordinary extension BY ZERO along the actual Gm -> A1 inclusion. -/
  affineZero : Obj .gm → Obj .line
  /-- Ordinary sheaf underlying the canonical middle extension across 0. -/
  affineMiddle : Obj .gm → Obj .line
  Hypergeometric : Obj .gm → ℕ → Prop
  NontrivialArtinSchreier : Obj .line → Prop

attribute [instance] GeometricModel.category GeometricModel.perverseCategory
  GeometricModel.perverseAbelian GeometricModel.zeroObject GeometricModel.gmGenericFinite

variable {K} (M : GeometricModel.{g,gh,h,hh} K) (U : UniformConstants)

/-- Explicit ORDINARY degree-zero concentration; this does not assert
lissity on all Gm. Balanced hypergeometric singularities at 1 are allowed. -/
def GeometricModel.gmOrdinary (A : M.Obj .gm) : Prop :=
  Nonempty (M.ordinary .gm A 0 ≅ A) ∧
    ∀ (d : ℤ), d ≠ 0 → Nonempty (M.ordinary .gm A d ≅ (0 : M.Obj .gm))

/-- Rank is the finite dimension of the SAME ordinary generic stalk. -/
def GeometricModel.genericRank (A : M.Obj .gm) : ℕ :=
  Module.finrank ℂ (M.gmGenericFiber A)

def GeometricModel.intermediate {i j} (f : scheme K i ⟶ scheme K j) (A : M.Perv i) :
    M.Perv j := Abelian.image ((M.openSupport f).app A)

/-- General published results: all constructible objects, all maps,
all degrees, all perverse morphisms, all admissible open maps/classes.
The image law is the perverse-subquotient consequence of QST 6.15. -/
structure PublishedLaws : Prop where
  iso : ∀ i {A B : M.Obj i}, (A ≅ B) → M.complexity i A = M.complexity i B
  /-- Geometric complexity invariance for EVERY constant rank-one twist.
  This is a geometric definition/isomorphism corollary, not an arithmetic unit iso. -/
  constant_tensor : ∀ i L A, M.GeometricConstantRankOne i L →
    M.complexity i (M.tensor i L A) = M.complexity i A
  shift : ∀ i A n, M.complexity i (M.shift i A n) = M.complexity i A
  twist : ∀ i A n, M.complexity i (M.twist i A n) = M.complexity i A
  dual : ∀ i A, M.complexity i (M.verdier i A) ≤
    U.dual (ambientDimension i) * M.embeddingComplexity i * M.complexity i A
  tensor : ∀ i A B, M.complexity i (M.tensor i A B) ≤
    U.tensor (ambientDimension i) * M.complexity i A * M.complexity i B
  unit : ∀ i, M.complexity i (M.unit i) = M.embeddingComplexity i
  pull : ∀ i j (f : scheme K i ⟶ scheme K j) A,
    M.complexity i (M.pull f A) ≤ U.pull (ambientDimension i) (ambientDimension j) *
      M.mapComplexity f * M.complexity j A
  push : ∀ i j (f : scheme K i ⟶ scheme K j) A,
    M.complexity j (M.push f A) ≤ U.push (ambientDimension i) (ambientDimension j) *
      M.mapComplexity f * M.complexity i A
  ordinary : ∀ i A d, M.complexity i (M.ordinary i A d) ≤
    U.ordinary (ambientDimension i) (M.complexity i A)
  image : ∀ i (A B : M.Perv i) (f : A ⟶ B),
    M.complexity i ((M.perverse i).obj (Abelian.image f)) ≤
      U.image (ambientDimension i) * M.embeddingComplexity i *
        M.complexity i ((M.perverse i).obj A)
  ic : ∀ i j (f : scheme K i ⟶ scheme K j), IsOpenImmersion f → M.Induced f →
    ∀ A, M.complexity j ((M.perverse j).obj (M.intermediate f A)) ≤
      U.ic (ambientDimension j) * (M.embeddingComplexity j * M.embeddingComplexity i)^2 *
        M.complexity i ((M.perverse i).obj A)
  hypergeometric : ∀ A r, M.Hypergeometric A r →
    M.complexity .gm A ≤ U.hypergeometric * r
  hypergeometric_ordinary : ∀ A r, M.Hypergeometric A r → M.gmOrdinary A
  hypergeometric_rank : ∀ A r, M.Hypergeometric A r → M.genericRank A = r
  affine_zero : ∀ A, M.complexity .line (M.affineZero A) = M.complexity .gm A
  /-- General one-boundary-point rank/triangle corollary for EVERY
  ordinary constructible Gm sheaf, including sheaves singular at 1.
  The added stalk at 0 is a subspace of the generic stalk. This is
  not a supplied Kl3 or family bound and needs no global lissity. -/
  affine_middle : ∀ A, M.gmOrdinary A →
    M.complexity .line (M.affineMiddle A) ≤ M.complexity .gm A + M.genericRank A
  artinSchreier : ∀ A, M.NontrivialArtinSchreier A → M.complexity .line A ≤ 1

/-- Uniform caps on these same FIXED presentations. They contain no
complexity bound on any selected sheaf, source recipe, or physical family. -/
structure FixedPresentationCaps : Prop where
  source : M.embeddingComplexity .source ≤ U.E6
  torus4 : M.embeddingComplexity .torus4 ≤ U.E4
  plane : M.embeddingComplexity .plane ≤ U.E2
  torus2 : M.embeddingComplexity .torus2 ≤ U.Ew
  projection : M.mapComplexity (i := .source) (j := .torus4)
    (SourceProjectionForQST.projection K) ≤ U.projection
  changeEmbedding : M.mapComplexity (i := .torus2) (j := .torus4)
    (𝟙 (PhysicalTorusMorphism.torusScheme K)) ≤ U.changeEmbedding

inductive Operation where
  | identity | sourceDual | sourceTensor | sourcePull | compact | image
  | torusPull | torusDual | torusTensor | ic
  deriving DecidableEq, Fintype

/-- Every formula is generated from the same dimension constants and
fixed caps. Signing is the identity formula because the SAME geometric
sign line is identified with the constant unit. -/
def rawBound (o : Operation) (n : ℕ) : ℕ :=
  match o with
  | .identity => n
  | .sourceDual => U.dual 6 * U.E6 * n
  | .sourceTensor => U.tensor 6 * n * n
  | .sourcePull => U.pull 6 1 * n * n
  | .compact => PublishedUniformComplexity.envelope (U.ordinary 4)
      (U.push 6 4 * U.projection * n)
  | .image => U.image 4 * U.E4 * n
  | .torusPull => U.pull 4 4 * n * n
  | .torusDual => U.dual 4 * U.E4 * n
  | .torusTensor => U.tensor 4 * n * n
  | .ic => U.ic 2 * (U.E2 * U.Ew)^2 * (U.pull 2 4 * U.changeEmbedding * n)

def maximumBound (n : ℕ) : ℕ := (Finset.univ : Finset Operation).sup (fun o => rawBound U o n)

def generatedBound (n : ℕ) : ℕ := PublishedUniformComplexity.envelope (maximumBound U) n

theorem rawBound_le_generated (o : Operation) {m n : ℕ} (hm : m ≤ n) :
    rawBound U o m ≤ generatedBound U n := by
  apply le_trans (Finset.le_sup (s := (Finset.univ : Finset Operation))
    (f := fun a => rawBound U a m) (Finset.mem_univ o))
  exact PublishedUniformComplexity.le_envelope (maximumBound U) hm

theorem generatedBound_mono : Monotone (generatedBound U) := by
  intro m n hmn
  exact PublishedUniformComplexity.envelope_mono (maximumBound U) hmn

universe v mu q pt
variable {p : ℕ} [Fact p.Prime] (B : System.{v,mu} (ZMod p))
  {Point : Type pt} (D : CurveData (B.Obj .source) Point)
  (H : CohomologyData (B.Obj .source) (B.Obj .torus))
  (P : ParameterData (B.Obj .torus))
  {Surface : Type q}
  {SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Surface}
  (R : PublishedSupportRules.RationalStalkRealization p SD)
  (E : IntermediateExtensionFromImage.Data R (B.Obj .torus))
  (signLine : B.Obj .torus)
  (SC : PrimitiveClasses (B.Obj .line))
  (ci : B.Obj .source → ℕ) (cp : B.Obj .torus → ℕ) (cl : B.Obj .line → ℕ)
  (cm : TorusMorphismComplexity (ZMod p)) (cs : MorphismComplexity (ZMod p))
  (G : GeometricModel.{g,gh,h,hh} (ZMod p))

/-- Common geometric equations, not target inequalities. The perverse
image comparison is guarded by BOTH original lissity predicates. Source
ordinary dual is D[-6](-3), and torus DT0 is D[-4](-3), retaining the
relative ordinary dual/Tate normalization. The compact object is ordinary
H1 of the actual pi! functor, and IC uses the original support arrow. -/
structure CommonRealization where
  line : B.Obj .line → G.Obj .line
  source : B.Obj .source → G.Obj .source
  torus : B.Obj .torus → G.Obj .torus4
  line_complexity : ∀ A, cl A = G.complexity .line (line A)
  source_complexity : ∀ A, ci A = G.complexity .source (source A)
  torus_complexity : ∀ A, cp A = G.complexity .torus4 (torus A)
  source_map : ∀ f, cs f = G.mapComplexity (i := .source) (j := .line) f
  torus_map : ∀ f, cm f = G.mapComplexity (i := .torus4) (j := .torus4) f
  source_dual : ∀ A, D.Lisse A → (source (D.dual A) ≅
    G.twist .source (G.shift .source (G.verdier .source (source A)) (-6)) (-3))
  source_tensor : ∀ A B, source (D.tensor A B) ≅ G.tensor .source (source A) (source B)
  source_pull : ∀ f A, source ((B.pull (X := .source) (Y := .line) f).obj A) ≅
    G.pull (i := .source) (j := .line) f (line A)
  compact : ∀ A, D.Lisse A → (torus (H.compact A) ≅
    G.ordinary .torus4 (G.push (i := .source) (j := .torus4)
      (SourceProjectionForQST.projection (ZMod p)) (source A)) 1)
  sign_geometrically_constant_rank_one : G.GeometricConstantRankOne .torus4 (torus signLine)
  signed : ∀ A, torus (P.signed A) ≅ G.tensor .torus4 (torus signLine) (torus A)
  torus_pull : ∀ f A, torus ((B.torusOperations.pullback f).obj A) ≅
    G.pull (i := .torus4) (j := .torus4) f (torus A)
  torus_dual : ∀ A, P.Lisse A → (torus (P.dualTateMinusOne A) ≅
    G.twist .torus4 (G.shift .torus4 (G.verdier .torus4 (torus A)) (-4)) (-3))
  torus_tensor : ∀ A B, torus (A ⊗ B) ≅ G.tensor .torus4 (torus A) (torus B)
  torus_unit : torus (𝟙_ (B.Obj .torus)) ≅ G.unit .torus4
  lissePerverse : B.Obj .torus ⥤ G.Perv .torus4
  /-- The general functor can be pH0(A[2]); this comparison is lisse-only. -/
  lisse_shift : ∀ A, P.Lisse A → ((G.perverse .torus4).obj (lissePerverse.obj A) ≅
    G.shift .torus4 (torus A) 2)
  lisse_image : ∀ A B (f : A ⟶ B), P.Lisse A → P.Lisse B →
    (G.shift .torus4 (torus (Abelian.image f)) 2 ≅
      (G.perverse .torus4).obj (Abelian.image (lissePerverse.map f)))
  openRealization : E.Open ⥤ G.Perv .torus2
  plane : E.Plane ⥤ G.Perv .plane
  [planeAdditive : plane.Additive]
  [planeLimits : PreservesFiniteLimits plane]
  [planeColimits : PreservesFiniteColimits plane]
  plane_complexity : ∀ A, SD.complexity (E.geometric A) =
    G.complexity .plane ((G.perverse .plane).obj (plane.obj A))
  zero : E.extensionByZero ⋙ plane ≅ openRealization ⋙
    G.openZero (i := .torus2) (j := .plane) (torusOpen (ZMod p))
  direct : E.directImage ⋙ plane ≅ openRealization ⋙
    G.openDirect (i := .torus2) (j := .plane) (torusOpen (ZMod p))
  support : ∀ A, plane.map (E.support.app A) ≫ (direct.app A).hom =
    (zero.app A).hom ≫ (G.openSupport (i := .torus2) (j := .plane)
      (torusOpen (ZMod p))).app (openRealization.obj A)
  open_shift : ∀ A, P.Lisse A →
    ((G.perverse .torus2).obj (openRealization.obj (E.perverseShift.obj A)) ≅
      G.shift .torus2 (G.pull (i := .torus2) (j := .torus4)
        (𝟙 (PhysicalTorusMorphism.torusScheme (ZMod p))) (torus A)) 2)
  openImmersion : IsOpenImmersion (torusOpen (ZMod p))
  inducedEmbedding : G.Induced (i := .torus2) (j := .plane) (torusOpen (ZMod p))
  hypergeometric : ∀ A r, SC.Hypergeometric A r → ∃ A0 : G.Obj .gm,
    G.Hypergeometric A0 r ∧
      (Nonempty (line A ≅ G.affineZero A0) ∨ Nonempty (line A ≅ G.affineMiddle A0))
  artinSchreier : ∀ A, SC.NontrivialArtinSchreier A → G.NontrivialArtinSchreier (line A)

attribute [instance] CommonRealization.planeAdditive CommonRealization.planeLimits
  CommonRealization.planeColimits

variable {B D H P R E signLine SC ci cp cl cm cs G}
  (C : CommonRealization B D H P R E signLine SC ci cp cl cm cs G)
  (L : PublishedLaws G U) (F : FixedPresentationCaps G U)

/-- Exactness and the original support equation derive the IC comparison;
no supplied comparison to a finished IC object is a realization field. -/
def CommonRealization.intermediateIso (A : E.Open) :
    C.plane.obj (E.intermediate A) ≅ G.intermediate (i := .torus2) (j := .plane)
      (torusOpen (ZMod p)) (C.openRealization.obj A) := by
  exact Abelian.PreservesImage.iso C.plane (E.support.app A) ≪≫
    Abelian.im.mapIso (Arrow.isoMk
      (f := Arrow.mk (C.plane.map (E.support.app A)))
      (g := Arrow.mk ((G.openSupport (i := .torus2) (j := .plane)
        (torusOpen (ZMod p))).app (C.openRealization.obj A)))
      (C.zero.app A) (C.direct.app A) (C.support A).symm)

private theorem product_bound (k a b n : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    k * a * b ≤ k * n * n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left k ha) hb

include C L F in
/-- Both former root records use this SAME generated envelope, optionally
dominated by an externally fixed old boundFn. All old domains and guards
are retained. No specialized target bound is an argument. -/
theorem operationBounds (f : ℕ → ℕ) (dominates : ∀ n, generatedBound U n ≤ f n)
    (unitCap : ℕ) (hunit : U.E4 ≤ unitCap) :
    OperationBounds (D := D) (H := H) (P := P) f unitCap ci cp cm B.torusOperations E.IC where
  input_dual A hA := by
    rw [C.source_complexity, L.iso _ (C.source_dual A hA), L.twist, L.shift]
    apply (L.dual .source _).trans
    apply le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ F.source))
    rw [← C.source_complexity]
    exact (rawBound_le_generated U .sourceDual (le_refl _)).trans (dominates _)
  input_tensor A B hA hB := by
    rw [C.source_complexity, L.iso _ (C.source_tensor A B)]
    apply (L.tensor .source _ _).trans
    apply le_trans (product_bound _ _ _ (max (ci A) (ci B))
      (by rw [← C.source_complexity A]; exact le_max_left _ _)
      (by rw [← C.source_complexity B]; exact le_max_right _ _))
    exact (rawBound_le_generated U .sourceTensor (le_refl _)).trans (dominates _)
  compact A hA := by
    rw [C.torus_complexity, L.iso _ (C.compact A hA)]
    apply (L.ordinary .torus4 _ 1).trans
    have hp : G.complexity .torus4 (G.push (i := .source) (j := .torus4)
        (SourceProjectionForQST.projection (ZMod p)) (C.source A)) ≤
        U.push 6 4 * U.projection * ci A := by
      apply (L.push .source .torus4 _ _).trans
      rw [← C.source_complexity]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ F.projection)
    apply le_trans (PublishedUniformComplexity.le_envelope (U.ordinary 4) hp)
    exact (rawBound_le_generated U .compact (le_refl _)).trans (dominates _)
  image A B g hA hB := by
    rw [C.torus_complexity, ← L.shift .torus4 _ 2, L.iso _ (C.lisse_image A B g hA hB)]
    apply (L.image .torus4 _ _ _).trans
    rw [L.iso _ (C.lisse_shift A hA), L.shift, ← C.torus_complexity]
    apply le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ F.torus4))
    exact (rawBound_le_generated U .image (le_refl _)).trans (dominates _)
  signed A hA := by
    rw [C.torus_complexity, L.iso _ (C.signed A)]
    rw [L.constant_tensor .torus4 _ _ C.sign_geometrically_constant_rank_one,
      ← C.torus_complexity]
    exact (rawBound_le_generated U .identity (le_refl _)).trans (dominates _)
  pullback g A hA := by
    rw [C.torus_complexity, L.iso _ (C.torus_pull g A)]
    apply (L.pull .torus4 .torus4 _ _).trans
    apply le_trans (product_bound _ _ _ (max (cm g) (cp A))
      (by rw [C.torus_map]; exact le_max_left _ _)
      (by rw [C.torus_complexity]; exact le_max_right _ _))
    exact (rawBound_le_generated U .torusPull (le_refl _)).trans (dominates _)
  dualTate A hA := by
    rw [C.torus_complexity, L.iso _ (C.torus_dual A hA), L.twist, L.shift]
    apply (L.dual .torus4 _).trans
    apply le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ F.torus4))
    rw [← C.torus_complexity]
    exact (rawBound_le_generated U .torusDual (le_refl _)).trans (dominates _)
  unit := by
    rw [C.torus_complexity, L.iso _ C.torus_unit, L.unit]
    exact F.torus4.trans hunit
  tensor A B hA hB := by
    rw [C.torus_complexity, L.iso _ (C.torus_tensor A B)]
    apply (L.tensor .torus4 _ _).trans
    apply le_trans (product_bound _ _ _ (max (cp A) (cp B))
      (by rw [← C.torus_complexity A]; exact le_max_left _ _)
      (by rw [← C.torus_complexity B]; exact le_max_right _ _))
    exact (rawBound_le_generated U .torusTensor (le_refl _)).trans (dominates _)
  ic A hA := by
    change SD.complexity (E.geometric (E.intermediate (E.perverseShift.obj A))) ≤ _
    rw [C.plane_complexity, L.iso _ ((G.perverse .plane).mapIso
      (C.intermediateIso (E.perverseShift.obj A)))]
    apply (L.ic .torus2 .plane _ C.openImmersion C.inducedEmbedding _).trans
    rw [L.iso _ (C.open_shift A hA), L.shift]
    have hchange : G.complexity .torus2 (G.pull (i := .torus2) (j := .torus4)
        (𝟙 (PhysicalTorusMorphism.torusScheme (ZMod p))) (C.torus A)) ≤
        U.pull 2 4 * U.changeEmbedding * cp A := by
      apply (L.pull .torus2 .torus4 _ _).trans
      rw [← C.torus_complexity]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ F.changeEmbedding)
    have he : (G.embeddingComplexity .plane * G.embeddingComplexity .torus2)^2 ≤
        (U.E2 * U.Ew)^2 := Nat.pow_le_pow_left (Nat.mul_le_mul F.plane F.torus2) 2
    apply le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ he) hchange)
    exact (rawBound_le_generated U .ic (le_refl _)).trans (dominates _)

include C L in
/-- QS is derived from the SAME model/constants/function as QB, for every
old primitive-class object and every source-to-line map. -/
theorem startingBounds (f : ℕ → ℕ) (dominates : ∀ n, generatedBound U n ≤ f n)
    (sourceCap0 : ℕ) (hsource : U.hypergeometric + 1 ≤ sourceCap0) :
    Bounds (FourierSourcePullbacks.originalPullbackData (ZMod p) B.geometricPullbacks)
      SC f sourceCap0 cl ci cs where
  hypergeometric A r hA := by
    rw [C.line_complexity]
    obtain ⟨A0, h0, hext⟩ := C.hypergeometric A r hA
    have hg := L.hypergeometric A0 r h0
    have he : G.complexity .line (C.line A) ≤ (U.hypergeometric + 1) * r := by
      rcases hext with hz | hm
      · obtain ⟨i⟩ := hz
        rw [L.iso _ i, L.affine_zero]
        exact hg.trans (Nat.mul_le_mul_right r (Nat.le_succ _))
      · obtain ⟨i⟩ := hm
        rw [L.iso _ i]
        apply (L.affine_middle A0 (L.hypergeometric_ordinary A0 r h0)).trans
        rw [L.hypergeometric_rank A0 r h0, add_mul, one_mul]
        exact Nat.add_le_add_right hg r
    exact he.trans (Nat.mul_le_mul_right r hsource)
  artinSchreier A hA := by
    rw [C.line_complexity]
    exact L.artinSchreier _ (C.artinSchreier A hA)
  pullback g A := by
    change ci ((B.pull (X := .source) (Y := .line) g).obj A) ≤ _
    rw [C.source_complexity, L.iso _ (C.source_pull g A)]
    apply (L.pull .source .line _ _).trans
    apply le_trans (product_bound _ _ _ (max (cs g) (cl A))
      (by rw [C.source_map]; exact le_max_left _ _)
      (by rw [C.line_complexity]; exact le_max_right _ _))
    exact (rawBound_le_generated U .sourcePull (le_refl _)).trans (dominates _)

/-- Fix U, f and BOTH scalar caps BEFORE quantifying over p. For every
prime and every same-object common realization, the exact old QB/QS
records follow. This conditional general application does not supply a
common realization for any prime or assert a complete compatible family.
The p-free TYPE of U alone would not enforce this quantifier order. -/
theorem uniform_application (U : UniformConstants) (f : ℕ → ℕ)
    (dominates : ∀ n, generatedBound U n ≤ f n)
    (unitCap : ℕ) (hunit : U.E4 ≤ unitCap)
    (sourceCap0 : ℕ) (hsource : U.hypergeometric + 1 ≤ sourceCap0) :
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (B : System.{v,mu} (ZMod p)) (Point : Type pt)
        (D : CurveData (B.Obj .source) Point)
        (H : CohomologyData (B.Obj .source) (B.Obj .torus))
        (P : ParameterData (B.Obj .torus))
        (Surface : Type q)
        (SD : PublishedSupportRules.SurfaceData (AlgebraicClosure (ZMod p)) Surface)
        (R : PublishedSupportRules.RationalStalkRealization p SD)
        (E : IntermediateExtensionFromImage.Data R (B.Obj .torus))
        (signLine : B.Obj .torus)
        (SC : PrimitiveClasses (B.Obj .line))
        (ci : B.Obj .source → ℕ) (cp : B.Obj .torus → ℕ) (cl : B.Obj .line → ℕ)
        (cm : TorusMorphismComplexity (ZMod p)) (cs : MorphismComplexity (ZMod p))
        (G : GeometricModel.{g,gh,h,hh} (ZMod p)),
        CommonRealization B D H P R E signLine SC ci cp cl cm cs G →
        PublishedLaws G U → FixedPresentationCaps G U →
          OperationBounds (D := D) (H := H) (P := P)
            f unitCap ci cp cm B.torusOperations E.IC ∧
          Bounds (FourierSourcePullbacks.originalPullbackData (ZMod p) B.geometricPullbacks)
            SC f sourceCap0 cl ci cs := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  intro B Point D H P Surface SD R E signLine SC ci cp cl cm cs G C L F
  exact ⟨operationBounds U C L F f dominates unitCap hunit,
    startingBounds U C L f dominates sourceCap0 hsource⟩

end PrimeGap182.TypeIII.UniformComplexityFromCommonRealization

#print axioms PrimeGap182.TypeIII.UniformComplexityFromCommonRealization.rawBound_le_generated
#print axioms PrimeGap182.TypeIII.UniformComplexityFromCommonRealization.generatedBound_mono
#print axioms PrimeGap182.TypeIII.UniformComplexityFromCommonRealization.CommonRealization.intermediateIso
#print axioms PrimeGap182.TypeIII.UniformComplexityFromCommonRealization.operationBounds
#print axioms PrimeGap182.TypeIII.UniformComplexityFromCommonRealization.startingBounds
#print axioms PrimeGap182.TypeIII.UniformComplexityFromCommonRealization.uniform_application
