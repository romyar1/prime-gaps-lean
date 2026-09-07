import TypeIIIEtaleSkyscraperFamily
import TypeIIIAlgebraicallyClosedEtalePoints
import Mathlib.CategoryTheory.Retract

/-!
# The canonical first Godement embedding and injective retract

Use the actual geometric point supplied by an algebraic closure of the
residue field at each point of the scheme.  The product of the original
skyscrapers of the original stalks receives the canonical stalk-adjunction
units.  On each of these stalks this map has an explicit retraction, given
by the corresponding product projection and the original counit.  The
proved conservativity of these points therefore makes the sheaf map mono.

An injective sheaf is consequently a retract of this actual product.
No splitting or embedding is assumed.  This is only the first Godement
embedding; no resolution or adic comparison is asserted here.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PrimeGap182.TypeIII.EtaleGodement

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry

variable (S : Scheme.{u}) (E : Type u) [Ring E]

/-- The actual product of skyscrapers of the original geometric stalks. -/
def obj (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} E) :=
  (EtaleSkyscraperFamily.functor S (algebraicClosureEtalePoint S) E).obj
    ((EtaleSkyscraperFamily.stalks S (algebraicClosureEtalePoint S) E).obj F)

/-- The product of the original stalk-adjunction unit maps. -/
def unit (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) : F ⟶ obj S E F :=
  Pi.lift (fun x =>
    (EtaleSkyscraper.adjunction S (algebraicClosureEtalePoint S x) E).unit.app F)

/-- Each product component is exactly the original adjunction unit. -/
@[simp]
theorem unit_π (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (x : S) :
    unit S E F ≫ Pi.π
      (EtaleSkyscraperFamily.skyscrapers S (algebraicClosureEtalePoint S) E
        ((EtaleSkyscraperFamily.stalks S (algebraicClosureEtalePoint S) E).obj F)) x =
      (EtaleSkyscraper.adjunction S (algebraicClosureEtalePoint S x) E).unit.app F :=
  Pi.lift_π _ x

/-- The original counit splits the stalk of the canonical embedding. -/
def stalkSplitting (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) (x : S) :
    SplitMono ((algebraicClosureEtalePoint S x).sheafFiber.map (unit S E F)) where
  retraction := (algebraicClosureEtalePoint S x).sheafFiber.map
      (Pi.π
        (EtaleSkyscraperFamily.skyscrapers S (algebraicClosureEtalePoint S) E
          ((EtaleSkyscraperFamily.stalks S (algebraicClosureEtalePoint S) E).obj F)) x) ≫
    (EtaleSkyscraper.adjunction S (algebraicClosureEtalePoint S x) E).counit.app
      ((algebraicClosureEtalePoint S x).sheafFiber.obj F)
  id := by
    rw [← assoc, ← Functor.map_comp, unit_π]
    exact (EtaleSkyscraper.adjunction S (algebraicClosureEtalePoint S x) E).left_triangle_components F

/-- The actual conservative geometric-point family detects that this
canonical sheaf map is a monomorphism. -/
instance unit_mono (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E)) :
    Mono (unit S E F) := by
  apply (((algebraicClosureEtalePoints_isConservative S).jointlyReflectMonomorphisms
    (ModuleCat.{u} E)).mono_iff (unit S E F)).2
  rintro ⟨_, ⟨x⟩⟩
  exact (stalkSplitting S E F x).mono

/-- Injectivity supplies a retraction of the proved canonical embedding. -/
def injectiveRetraction (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    [Injective F] : obj S E F ⟶ F :=
  Injective.factorThru (𝟙 F) (unit S E F)

/-- The chosen injective retraction splits the original canonical unit. -/
@[simp]
theorem unit_injectiveRetraction (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    [Injective F] : unit S E F ≫ injectiveRetraction S E F = 𝟙 F :=
  Injective.comp_factorThru (𝟙 F) (unit S E F)

/-- Every actual injective sheaf is a retract of this actual product of
skyscrapers of its geometric stalks. -/
def injectiveRetract (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} E))
    [Injective F] : Retract F (obj S E F) where
  i := unit S E F
  r := injectiveRetraction S E F
  retract := unit_injectiveRetraction S E F

#print axioms obj
#print axioms unit
#print axioms unit_π
#print axioms stalkSplitting
#print axioms unit_mono
#print axioms injectiveRetraction
#print axioms unit_injectiveRetraction
#print axioms injectiveRetract

end PrimeGap182.TypeIII.EtaleGodement
