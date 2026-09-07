import TypeIIIArtinSchreierPointStalk

/-!
# A conservative family of algebraically closed geometric points

Choose the algebraic closure of the residue field at every point of a
scheme. The resulting actual small-étale points are conservative. This
allows the proved algebraically closed Artin--Schreier stalk comparisons
to detect sheaf isomorphisms; no extra stalk-detection premise is needed.
-/

noncomputable section

universe u

namespace PrimeGap182.TypeIII

open CategoryTheory AlgebraicGeometry

/-- The canonical geometric point obtained from an algebraic closure of
the actual residue field at a scheme point. -/
def algebraicClosureEtalePointMap (S : Scheme.{u}) (s : S) :
    Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  (Scheme.SpecToEquivOfField (AlgebraicClosure (S.residueField s)) S).symm
    ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s) _)⟩

/-- This is a geometric point over the specified point of the scheme. -/
@[simp] theorem algebraicClosureEtalePointMap_apply (S : Scheme.{u}) (s : S)
    (x : Spec (.of (AlgebraicClosure (S.residueField s)))) :
    algebraicClosureEtalePointMap S s x = s := by
  simp [algebraicClosureEtalePointMap, Scheme.SpecToEquivOfField]

/-- The actual point of the small étale site supplied by that field. -/
def algebraicClosureEtalePoint (S : Scheme.{u}) (s : S) :
    GrothendieckTopology.Point.{u} S.smallEtaleTopology :=
  Scheme.pointSmallEtale (algebraicClosureEtalePointMap S s)

/-- The algebraically closed geometric points detect the covering
sieves, and hence form a conservative family of actual site points. -/
theorem algebraicClosureEtalePoints_isConservative (S : Scheme.{u}) :
    (ObjectProperty.ofObj (algebraicClosureEtalePoint S)).IsConservativeFamilyOfPoints := by
  exact Scheme.isConservative_pointSmallEtale (algebraicClosureEtalePointMap S) (by
    ext s
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, algebraicClosureEtalePointMap_apply S s default⟩)

#print axioms algebraicClosureEtalePointMap
#print axioms algebraicClosureEtalePointMap_apply
#print axioms algebraicClosureEtalePoint
#print axioms algebraicClosureEtalePoints_isConservative

end PrimeGap182.TypeIII
