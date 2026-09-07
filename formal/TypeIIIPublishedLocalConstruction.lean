import TypeIIIPublishedMackey

/-!
# Constructing the local Type III input from general published laws

The infinity-to-zero local Fourier operation includes pullback by ξ=T²/A
and restriction to wild inertia at T=0.  It is defined only on admissible
inertia representations and at nonzero A.  In the intended realization,
admissibility is the continuity and finite coefficient-field condition in
Laumon, §2.1.2.  Its output on a cubic character is *defined* to be the
`CubicFourierData` used by Fu's general rule.  The value at A=0 is an unused
zero representation, not an extension of the local Fourier functor.

`FiniteOriginData` records the natural maps for an arbitrary one-dimensional
perverse object.  `FiniteOriginRules` is the finite-origin vanishing-cycle
sequence in Laumon, §2.3.2 (pp. 159--160), with Proposition 2.3.2.1(iii)
and Lemma 2.4.2.1(ii) identifying its local term.  The natural arrow goes
from the generic Fourier stalk to the local transform.  Its remaining
target comes from a closed-point stalk, hence is geometrically constant.
The maps and their functorial geometric realization remain external data;
the general exactness theorem is an explicit hypothesis.

For a particular perverse object, callers now supply its infinity
representation and its generic rank.  The Mackey/local-Fourier comparison,
the correct finite-origin map and its exactness are obtained from the
general laws rather than supplied as family-specific `CoreLocalData`.
Identifying this perverse object and generic stalk with the physical
parabolic correlation family remains an explicit realization obligation.

References:
* Laumon, https://www.numdam.org/article/PMIHES_1987__65__131_0.pdf,
  §2.3.2, Proposition 2.3.2.1(iii), Lemma 2.4.2.1(ii), Theorem 2.4.3(ii)(a).
* Fu, https://arxiv.org/pdf/math/0702436v5, Proposition 0.8 and
  Theorem 0.1(iii), with r=3,s=1 and characteristic p>3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical

namespace PrimeGap182.TypeIII.PublishedLocalConstruction

open PublishedPhaseApplication PublishedMackey

universe u v w z t q

variable {K : Type u} [Field K] {E : Type v} [Field E] [CharZero E]
  {I : Type w} [Group I] {H : Type z} [Group H] {G : Type t} [Group G]

/-- A functor on a specified full subcategory of actual finite-dimensional
representations.  Objects require an admissibility witness; morphisms are
the actual equivariant linear maps between those objects. -/
structure AdmissibleRepresentationFunctor (E : Type v) [Field E]
    (I : Type w) [Group I] (G : Type t) [Group G]
    (Admissible : FDRep E I → Prop) where
  obj : (R : FDRep E I) → Admissible R → FDRep E G
  map : ∀ {R S : FDRep E I} (hR : Admissible R) (hS : Admissible S),
    Representation.IntertwiningMap R.ρ S.ρ →
    Representation.IntertwiningMap (obj R hR).ρ (obj S hS).ρ
  map_id : ∀ (R : FDRep E I) (hR : Admissible R),
    map hR hR (Representation.IntertwiningMap.id R.ρ) =
      Representation.IntertwiningMap.id (obj R hR).ρ
  map_comp : ∀ {R S T : FDRep E I}
    (hR : Admissible R) (hS : Admissible S) (hT : Admissible T),
    ∀ f : Representation.IntertwiningMap R.ρ S.ρ,
    ∀ g : Representation.IntertwiningMap S.ρ T.ρ,
      map hR hT (g.comp f) = (map hS hT g).comp (map hR hS f)

/-- An equivalence between admissible representations is carried to an
equivalence by the actual action on maps and the functor laws. -/
def AdmissibleRepresentationFunctor.mapEquiv {Admissible : FDRep E I → Prop}
    (F : AdmissibleRepresentationFunctor E I G Admissible)
    {R S : FDRep E I} (hR : Admissible R) (hS : Admissible S)
    (f : Representation.Equiv R.ρ S.ρ) :
    Representation.Equiv (F.obj R hR).ρ (F.obj S hS).ρ := by
  have hleft : f.symm.toIntertwiningMap.comp f.toIntertwiningMap =
      Representation.IntertwiningMap.id R.ρ := by
    ext x
    exact f.toLinearEquiv.symm_apply_apply x
  have hright : f.toIntertwiningMap.comp f.symm.toIntertwiningMap =
      Representation.IntertwiningMap.id S.ρ := by
    ext x
    exact f.toLinearEquiv.apply_symm_apply x
  have hl := congrArg (fun h => h.toLinearMap) (F.map_comp hR hS hR
    f.toIntertwiningMap f.symm.toIntertwiningMap)
  have hr := congrArg (fun h => h.toLinearMap) (F.map_comp hS hR hS
    f.symm.toIntertwiningMap f.toIntertwiningMap)
  rw [hleft, F.map_id] at hl
  rw [hright, F.map_id] at hr
  exact {
    toLinearEquiv := LinearEquiv.ofLinearMap
      (F.map hR hS f.toIntertwiningMap).toLinearMap
      (F.map hS hR f.symm.toIntertwiningMap).toLinearMap hr.symm hl.symm
    isIntertwining' := (F.map hR hS f.toIntertwiningMap).isIntertwining' }

/-- The actual local Fourier functor on admissible inertia representations,
followed by ξ=T²/A and wild restriction, for nonzero A.  The intended
admissibility predicate is Laumon's continuous, finite coefficient-field
category (§2.1.2); no operation on arbitrary abstract representations is
assumed.  The action on maps and functor laws are part of the data. -/
structure LocalFourierData (K : Type u) [Field K] (E : Type v) [Field E]
    (I : Type w) [Group I] (G : Type t) [Group G] where
  Admissible : FDRep E I → Prop
  operation : (a : PhaseField K) → a ≠ 0 →
    AdmissibleRepresentationFunctor E I G Admissible

/-- Finite direct-sum compatibility of the general local Fourier functor.
It follows from Laumon Theorem 2.4.3(ii)(a); the two subsequent pullback and
restriction functors also preserve finite direct sums. -/
structure LocalFourierAdditivity (F : LocalFourierData K E I G) where
  admissible_equiv : ∀ {R S : FDRep E I}, Representation.Equiv R.ρ S.ρ →
    F.Admissible R → F.Admissible S
  admissible_sum : ∀ {ι : Type} [Fintype ι], ∀ R : ι → FDRep E I,
    (∀ i, F.Admissible (R i)) → F.Admissible (finiteSum R)
  sum : ∀ (a : PhaseField K) (ha : a ≠ 0), ∀ {ι : Type} [Fintype ι],
    ∀ (R : ι → FDRep E I) (hR : ∀ i, F.Admissible (R i)),
    Representation.Equiv
      ((F.operation a ha).obj (finiteSum R) (admissible_sum R hR)).ρ
      (finiteSum (fun i => (F.operation a ha).obj (R i) (hR i))).ρ

/-- Linear Artin--Schreier characters and their finite cubic pushforwards
belong to Laumon's admissible category.  This generic lissity law has no
reference to the correlation family or its phase decomposition. -/
structure CubicInputAdmissibility (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H) (F : LocalFourierData K E I G) : Prop where
  push_phase : ∀ c : PhaseField K, F.Admissible (P.push.obj (A.phase c))

/-- Fu's cubic operation is this literal composite of functors. There
is no supplied identification of the finished correlation's phase list. -/
def cubicFourierData (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H) (F : LocalFourierData K E I G)
    (FA : CubicInputAdmissibility P A F) :
    CubicFourierData K E G where
  output a r := if ha : a ≠ 0 then
      (F.operation a ha).obj (P.push.obj (A.phase (3 * (1 - r)))) (FA.push_phase _)
    else finiteSum (fun i : Fin 0 => Fin.elim0 i)

omit [CharZero E] in
/-- At every scale used by Fu's rule, the cubic output is the literal
local transform of its admissible cubic pushforward. -/
theorem cubicFourierData_output (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H) (F : LocalFourierData K E I G)
    (FA : CubicInputAdmissibility P A F) (a r : PhaseField K) (ha : a ≠ 0) :
    (cubicFourierData P A F FA).output a r =
      (F.operation a ha).obj (P.push.obj (A.phase (3 * (1 - r)))) (FA.push_phase _) := by
  simp only [cubicFourierData, dite_eq_left ha]

/-- The correlation is admissible by its proved Mackey decomposition
and the generic closure laws.  Its admissibility is not a new hypothesis. -/
theorem correlation_admissible (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H)
    (D : KloostermanInfinityData (PhaseField K) E I)
    (F : LocalFourierData K E I G)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (KR : KloostermanInfinityRules p P A D) (FR : LocalFourierAdditivity F)
    (FA : CubicInputAdmissibility P A F)
    (hp : 3 < p) (c r : PhaseField K) (hr : r ≠ 0) (hcube : r ^ 3 = c) :
    F.Admissible (tensor (D.kl 1) (dualRepresentation (D.kl c))) :=
  FR.admissible_equiv
    (kloosterman_correlation_mackey p P A D PR AR KR hp c r hr hcube).symm
    (FR.admissible_sum (fun i => P.push.obj (A.phase (3 * (1 - cubicBranch P r i))))
      (fun _ => FA.push_phase _))

/-- The actual local transform of the correlation representation is
the direct sum of the three literal cubic local transforms. -/
def correlation_fourier_mackey (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H)
    (D : KloostermanInfinityData (PhaseField K) E I)
    (F : LocalFourierData K E I G)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (KR : KloostermanInfinityRules p P A D) (FR : LocalFourierAdditivity F)
    (FA : CubicInputAdmissibility P A F)
    (hp : 3 < p) (a c r : PhaseField K) (ha : a ≠ 0) (hr : r ≠ 0) (hcube : r ^ 3 = c) :
    Representation.Equiv
      ((F.operation a ha).obj (tensor (D.kl 1) (dualRepresentation (D.kl c)))
        (correlation_admissible p P A D F PR AR KR FR FA hp c r hr hcube)).ρ
      (finiteSum (fun i => (cubicFourierData P A F FA).output a (cubicBranch P r i))).ρ := by
  have houtputs :
      (fun i : Fin 3 => (cubicFourierData P A F FA).output a (cubicBranch P r i)) =
      (fun i : Fin 3 => (F.operation a ha).obj
        (P.push.obj (A.phase (3 * (1 - cubicBranch P r i)))) (FA.push_phase _)) := by
    funext i
    exact cubicFourierData_output P A F FA a (cubicBranch P r i) ha
  rw [houtputs]
  exact
    ((F.operation a ha).mapEquiv
      (correlation_admissible p P A D F PR AR KR FR FA hp c r hr hcube)
      (FR.admissible_sum (fun i => P.push.obj (A.phase (3 * (1 - cubicBranch P r i))))
        (fun _ => FA.push_phase _))
      (kloosterman_correlation_mackey p P A D PR AR KR hp c r hr hcube)).trans
      (FR.sum a ha (fun i => P.push.obj (A.phase (3 * (1 - cubicBranch P r i))))
        (fun _ => FA.push_phase _))

/-- Generic angular value of the scalar pullback in the correlation. -/
def angularRatio (m n : K) : PhaseField K :=
  algebraMap K (PhaseField K) (m / n) / direction K ^ 3

theorem angularRatio_ne_zero (m n : K) (hm : m ≠ 0) (hn : n ≠ 0) :
    angularRatio m n ≠ 0 := by
  apply div_ne_zero
  · simpa only [map_zero] using
      (algebraMap K (PhaseField K)).injective.ne (div_ne_zero hm hn)
  · exact pow_ne_zero 3 direction_ne_zero

/-- One root exists in the actual algebraic closure of the direction field. -/
def angularCubeRoot (m n : K) : PhaseField K :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (angularRatio m n) (by decide : 0 < 3))

theorem angularCubeRoot_cube (m n : K) : angularCubeRoot m n ^ 3 = angularRatio m n :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (angularRatio m n) (by decide : 0 < 3))

theorem angularCubeRoot_ne_zero (m n : K) (hm : m ≠ 0) (hn : n ≠ 0) :
    angularCubeRoot m n ≠ 0 := by
  intro hzero
  have h := angularCubeRoot_cube m n
  rw [hzero, zero_pow (by decide : 3 ≠ 0)] at h
  exact angularRatio_ne_zero m n hm hn h.symm

/-- Natural finite-origin vanishing-cycle maps of arbitrary perverse
objects on A¹. Here Q is the type of those perverse objects in the
intended realization; infinity is their generic infinity representation,
origin their generic Fourier representation after ξ=T²/A, and boundary
the degree-zero closed-point stalk after the same pullback. -/
structure FiniteOriginData (Q : Type q) (F : LocalFourierData K E I G) where
  infinity : Q → FDRep E I
  infinity_admissible : ∀ P, F.Admissible (infinity P)
  origin : (a : PhaseField K) → a ≠ 0 → Q → FDRep E G
  boundary : (a : PhaseField K) → a ≠ 0 → Q → FDRep E G
  toVanishing : ∀ (a : PhaseField K) (ha : a ≠ 0) P,
    Representation.IntertwiningMap (origin a ha P).ρ
      ((F.operation a ha).obj (infinity P) (infinity_admissible P)).ρ
  toBoundary : ∀ (a : PhaseField K) (ha : a ≠ 0) P,
    Representation.IntertwiningMap
      ((F.operation a ha).obj (infinity P) (infinity_admissible P)).ρ
      (boundary a ha P).ρ

/-- The relevant portion of Laumon's finite-origin exact sequence,
for arbitrary perverse objects and nonzero radial scale.  The target is
the closed-point stalk, hence wild inertia acts trivially on it.
The rank of a particular family's origin representation is not a field. -/
structure FiniteOriginRules (p : ℕ) [Fact p.Prime] [CharP K p]
    {Q : Type q} {F : LocalFourierData K E I G} (D : FiniteOriginData Q F) : Prop where
  exact : 3 < p → ∀ (a : PhaseField K) (ha : a ≠ 0) P,
    LinearMap.range (D.toVanishing a ha P).toLinearMap =
      LinearMap.ker (D.toBoundary a ha P).toLinearMap
  constant : 3 < p → ∀ (a : PhaseField K) (ha : a ≠ 0) P,
    Representation.IsTrivial (D.boundary a ha P).ρ

/-- Build the formerly supplied local data from the general published
laws.  The infinity model and rank belong to this perverse object; its
finite-origin map is the very map in the generic vanishing-cycle data.
The three-block comparison is proved by the Mackey calculation above. -/
def coreLocalDataOfPublished (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H)
    (D : KloostermanInfinityData (PhaseField K) E I)
    (F : LocalFourierData K E I G)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (KR : KloostermanInfinityRules p P A D) (FR : LocalFourierAdditivity F)
    (FA : CubicInputAdmissibility P A F)
    {Q : Type q} (S : FiniteOriginData Q F) (SR : FiniteOriginRules p S)
    (hp : 3 < p) (α m n : K) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (X : Q)
    (hinfinity : Representation.Equiv (S.infinity X).ρ
      (tensor (D.kl 1) (dualRepresentation (D.kl (angularRatio m n)))).ρ)
    (hrank : Module.finrank E
      (S.origin (radialScale α m) (radialScale_ne_zero α m hα hm) X) = 6) :
    CoreLocalData (cubicFourierData P A F FA) α m n
      (S.origin (radialScale α m) (radialScale_ne_zero α m hα hm) X) where
  q := cubicBranch P (angularCubeRoot m n)
  q_cube := fun i => cubicBranch_cube P (angularRatio m n) (angularCubeRoot m n)
    (angularCubeRoot_cube m n) i
  V := (F.operation (radialScale α m) (radialScale_ne_zero α m hα hm)).obj
    (S.infinity X) (S.infinity_admissible X)
  T := S.boundary (radialScale α m) (radialScale_ne_zero α m hα hm) X
  mackeyFourierComparison :=
    ((F.operation (radialScale α m) (radialScale_ne_zero α m hα hm)).mapEquiv
      (S.infinity_admissible X)
      (correlation_admissible p P A D F PR AR KR FR FA hp
        (angularRatio m n) (angularCubeRoot m n)
        (angularCubeRoot_ne_zero m n hm hn) (angularCubeRoot_cube m n))
      hinfinity).trans
      (correlation_fourier_mackey p P A D F PR AR KR FR FA hp (radialScale α m)
        (angularRatio m n) (angularCubeRoot m n) (radialScale_ne_zero α m hα hm)
        (angularCubeRoot_ne_zero m n hm hn)
        (angularCubeRoot_cube m n))
  toVanishing := S.toVanishing (radialScale α m) (radialScale_ne_zero α m hα hm) X
  toTame := S.toBoundary (radialScale α m) (radialScale_ne_zero α m hα hm) X
  exact := SR.exact hp (radialScale α m) (radialScale_ne_zero α m hα hm) X
  tame := SR.constant hp (radialScale α m) (radialScale_ne_zero α m hα hm) X
  core_rank := hrank

/-- The generic published cover, Kloosterman and finite-origin laws now
give the exhaustive core profile, after the perverse-object realization
supplies its infinity identification and rank.  No family-specific exact
sequence, Mackey comparison, or final phase list is a hypothesis here. -/
theorem core_profile_of_published [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : CubicCoverData (PhaseField K) E I H)
    (A : LinearASData (PhaseField K) E H)
    (D : KloostermanInfinityData (PhaseField K) E I)
    (F : LocalFourierData K E I G)
    (PR : CubicCoverRules P) (AR : LinearASRules P A)
    (KR : KloostermanInfinityRules p P A D) (FR : LocalFourierAdditivity F)
    (FA : CubicInputAdmissibility P A F)
    {Q : Type q} (S : FiniteOriginData Q F) (SR : FiniteOriginRules p S)
    (profile : PhaseData K E G) (phaseRules : PhaseRules profile)
    (fu : FuRules p profile (cubicFourierData P A F FA))
    (hp : 3 < p) (h2 : (2 : K) ≠ 0)
    (α m n : K) (hα : α ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (X : Q)
    (hinfinity : Representation.Equiv (S.infinity X).ρ
      (tensor (D.kl 1) (dualRepresentation (D.kl (angularRatio m n)))).ρ)
    (hrank : Module.finrank E
      (S.origin (radialScale α m) (radialScale_ne_zero α m hα hm) X) = 6) :
    profile.HasProfile
        (S.origin (radialScale α m) (radialScale_ne_zero α m hα hm) X) ∧
      ∀ β ∈ profile.phases
          (S.origin (radialScale α m) (radialScale_ne_zero α m hα hm) X),
        FuCubicSquaredPhase α m n β :=
  core_profile_of_local_data phaseRules fu hp h2 α m n hα hm _
    (coreLocalDataOfPublished p P A D F PR AR KR FR FA S SR hp α m n hα hm hn X hinfinity hrank)

end PrimeGap182.TypeIII.PublishedLocalConstruction

#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.mapEquiv
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.CubicInputAdmissibility
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.cubicFourierData
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.cubicFourierData_output
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.correlation_admissible
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.correlation_fourier_mackey
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.angularRatio
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.angularRatio_ne_zero
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.angularCubeRoot
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.angularCubeRoot_cube
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.angularCubeRoot_ne_zero
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.coreLocalDataOfPublished
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.core_profile_of_published

/- Generated declarations are included in the axiom audit. -/
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.casesOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.map
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.map_comp
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.map_id
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.mk
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.obj
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.rec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.AdmissibleRepresentationFunctor.recOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.CubicInputAdmissibility.casesOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.CubicInputAdmissibility.mk
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.CubicInputAdmissibility.push_phase
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.CubicInputAdmissibility.rec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.CubicInputAdmissibility.recOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.boundary
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.infinity
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.infinity_admissible
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.mk
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.origin
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.rec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.recOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.toBoundary
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginData.toVanishing
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules.casesOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules.constant
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules.exact
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules.mk
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules.rec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.FiniteOriginRules.recOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.casesOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.admissible_equiv
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.admissible_sum
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.mk
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.rec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.recOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierAdditivity.sum
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.casesOn
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.Admissible
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.ctorIdx
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.mk
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.mk.inj
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.mk.injEq
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.mk.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.mk.sizeOf_spec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.noConfusion
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.noConfusionType
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.operation
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.rec
#print axioms PrimeGap182.TypeIII.PublishedLocalConstruction.LocalFourierData.recOn
