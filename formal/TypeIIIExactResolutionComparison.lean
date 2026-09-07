import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Comparison from an exact complex to an injective resolution

An exact augmented nonnegative cochain complex maps to an actual
injective resolution, extending any map of the augmented objects.
Any two such extensions are homotopic.  The source objects are not
assumed injective: the recursive construction uses exactness of the
source and injectivity of the target objects only.

The construction generalizes the recursions in Mathlib's
`CategoryTheory.InjectiveResolution.desc` and `descHomotopy` to an
unbundled exact source.  All complexes and homotopies are the existing
Mathlib objects.  No base-change or geometric isomorphism is asserted.
-/

noncomputable section

universe v u

namespace PrimeGap182.TypeIII

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {A B : C}

set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-zero extension uses only the monomorphic source augmentation
and the injective degree-zero target. -/
def exactResolutionComparisonFZero (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    [Mono ι] (f : A ⟶ B) (J : InjectiveResolution B) : K.X 0 ⟶ J.cocomplex.X 0 :=
  Injective.factorThru (f ≫ J.ι.f 0) ι

set_option backward.isDefEq.respectTransparency false in
/-- Source exactness at degree zero extends the first commuting square. -/
def exactResolutionComparisonFOne (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    [Mono ι] (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (f : A ⟶ B) (J : InjectiveResolution B) : K.X 1 ⟶ J.cocomplex.X 1 :=
  h₀.descToInjective (exactResolutionComparisonFZero K ι f J ≫ J.cocomplex.d 0 1) (by
    change ι ≫ (exactResolutionComparisonFZero K ι f J ≫ J.cocomplex.d 0 1) = 0
    rw [← assoc, exactResolutionComparisonFZero, Injective.comp_factorThru, assoc]
    have hJ : (J.ι.f 0 : B ⟶ J.cocomplex.X 0) ≫ J.cocomplex.d 0 1 = 0 :=
      J.ι_f_zero_comp_complex_d
    rw [hJ, comp_zero])

@[reassoc (attr := simp)]
theorem exactResolutionComparisonFOne_comm (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    [Mono ι] (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (f : A ⟶ B) (J : InjectiveResolution B) :
    K.d 0 1 ≫ exactResolutionComparisonFOne K ι w h₀ f J =
      exactResolutionComparisonFZero K ι f J ≫ J.cocomplex.d 0 1 :=
  h₀.comp_descToInjective _ _

/-- The induction step uses exactness at the next source object and
injectivity of the next target object. -/
def exactResolutionComparisonFSucc (K : CochainComplex C ℕ)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (J : InjectiveResolution B) (n : ℕ)
    (g : K.X n ⟶ J.cocomplex.X n) (g' : K.X (n + 1) ⟶ J.cocomplex.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ J.cocomplex.d n (n + 1)) :
    Σ' g'' : K.X (n + 2) ⟶ J.cocomplex.X (n + 2),
      K.d (n + 1) (n + 2) ≫ g'' = g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  ⟨(hpos n).descToInjective (g' ≫ J.cocomplex.d (n + 1) (n + 2))
      (by simp [reassoc_of% w]), (hpos n).comp_descToInjective _ _⟩

/-- An actual chain map from an exact augmented source to the actual
injective resolution of the target object. -/
def exactResolutionComparison (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    [Mono ι] (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (f : A ⟶ B) (J : InjectiveResolution B) : K ⟶ J.cocomplex :=
  CochainComplex.mkHom K J.cocomplex (exactResolutionComparisonFZero K ι f J)
    (exactResolutionComparisonFOne K ι w h₀ f J)
    (exactResolutionComparisonFOne_comm K ι w h₀ f J).symm
    (fun n ⟨g, g', w'⟩ =>
      ⟨(exactResolutionComparisonFSucc K hpos J n g g' w'.symm).1,
        (exactResolutionComparisonFSucc K hpos J n g g' w'.symm).2.symm⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual comparison extends the given map on the augmented objects. -/
@[reassoc (attr := simp)]
theorem exactResolutionComparison_commutes (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    [Mono ι] (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (f : A ⟶ B) (J : InjectiveResolution B) :
    ι ≫ (exactResolutionComparison K ι w h₀ hpos f J).f 0 = f ≫ J.ι.f 0 := by
  simp only [exactResolutionComparison, CochainComplex.mkHom_f_0,
    exactResolutionComparisonFZero, Injective.comp_factorThru]

/-- The first null-homotopy component is obtained from source exactness
and injectivity of degree zero of the target. -/
def exactResolutionHomotopyZeroZero (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (ha : ι ≫ a.f 0 = 0) :
    K.X 1 ⟶ J.cocomplex.X 0 :=
  h₀.descToInjective (a.f 0) ha

@[reassoc (attr := simp)]
theorem exactResolutionHomotopyZeroZero_comp (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (ha : ι ≫ a.f 0 = 0) :
    K.d 0 1 ≫ exactResolutionHomotopyZeroZero K ι w h₀ J a ha = a.f 0 :=
  h₀.comp_descToInjective _ _

/-- The second null-homotopy component uses exactness at source degree one. -/
def exactResolutionHomotopyZeroOne (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (ha : ι ≫ a.f 0 = 0) :
    K.X 2 ⟶ J.cocomplex.X 1 :=
  (hpos 0).descToInjective
    (a.f 1 - exactResolutionHomotopyZeroZero K ι w h₀ J a ha ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, exactResolutionHomotopyZeroZero_comp_assoc,
      HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
theorem exactResolutionHomotopyZeroOne_comp (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (ha : ι ≫ a.f 0 = 0) :
    K.d 1 2 ≫ exactResolutionHomotopyZeroOne K ι w h₀ hpos J a ha =
      a.f 1 - exactResolutionHomotopyZeroZero K ι w h₀ J a ha ≫ J.cocomplex.d 0 1 :=
  (hpos 0).comp_descToInjective _ _

/-- The recursive null-homotopy extension needs no injectivity in the source. -/
def exactResolutionHomotopyZeroSucc (K : CochainComplex C ℕ)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ J.cocomplex.X n) (g' : K.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : a.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    K.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (hpos (n + 1)).descToInjective (a.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
    dsimp
    rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
      assoc, assoc, HomologicalComplex.d_comp_d, comp_zero, add_zero, sub_self])

@[reassoc (attr := simp)]
theorem exactResolutionHomotopyZeroSucc_comp (K : CochainComplex C ℕ)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ J.cocomplex.X n) (g' : K.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : a.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ exactResolutionHomotopyZeroSucc K hpos J a n g g' w =
      a.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  (hpos (n + 1)).comp_descToInjective _ _

/-- A map out of the exact source that vanishes on its augmentation is
actually null-homotopic in the injective target. -/
def exactResolutionHomotopyZero (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (J : InjectiveResolution B) (a : K ⟶ J.cocomplex) (ha : ι ≫ a.f 0 = 0) :
    Homotopy a 0 :=
  Homotopy.mkCoinductive a (exactResolutionHomotopyZeroZero K ι w h₀ J a ha) (by simp)
    (exactResolutionHomotopyZeroOne K ι w h₀ hpos J a ha) (by simp)
    (fun n ⟨g, g', w'⟩ =>
      ⟨exactResolutionHomotopyZeroSucc K hpos J a n g g' (by simp only [w', add_comm]),
        by simp⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-- Any two actual comparison maps extending the same augmentation map
are homotopic.  Injectivity of the source terms is not required. -/
def exactResolutionComparisonHomotopy (K : CochainComplex C ℕ) (ι : A ⟶ K.X 0)
    (w : ι ≫ K.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
    (f : A ⟶ B) (J : InjectiveResolution B) (a b : K ⟶ J.cocomplex)
    (ha : ι ≫ a.f 0 = f ≫ J.ι.f 0) (hb : ι ≫ b.f 0 = f ≫ J.ι.f 0) :
    Homotopy a b :=
  Homotopy.equivSubZero.invFun (exactResolutionHomotopyZero K ι w h₀ hpos J (a - b) (by
    change ι ≫ (a.f 0 - b.f 0) = 0
    rw [Preadditive.comp_sub, ha, hb, sub_self]))

#print axioms exactResolutionComparisonFZero
#print axioms exactResolutionComparisonFOne
#print axioms exactResolutionComparisonFOne_comm
#print axioms exactResolutionComparisonFSucc
#print axioms exactResolutionComparison
#print axioms exactResolutionComparison_commutes
#print axioms exactResolutionHomotopyZeroZero
#print axioms exactResolutionHomotopyZeroZero_comp
#print axioms exactResolutionHomotopyZeroOne
#print axioms exactResolutionHomotopyZeroOne_comp
#print axioms exactResolutionHomotopyZeroSucc
#print axioms exactResolutionHomotopyZeroSucc_comp
#print axioms exactResolutionHomotopyZero
#print axioms exactResolutionComparisonHomotopy

end PrimeGap182.TypeIII
