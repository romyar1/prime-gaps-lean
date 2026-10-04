import TypeIIIParabolicBaseChange

/-!
# Ordinary base change from compact base change and relative duality

Only lisse inputs tame at zero and isoclinic of slope one at infinity
are used. Their compact cohomology and that of their dual are lisse by
the existing constant-conductor law. Relative duality and compact base
change then construct ordinary base change. Naturality of the compact
pairing gives compatibility with the original support-forgetting map.

The compact base-change, canonical duality and pairing laws remain
general published inputs for a compatible geometric realization. No
ordinary base-change map or parabolic-image comparison is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality

open PublishedPhysicalConstruction ParabolicBaseChange

universe u v w z a b c d e
variable {Input : Type u} {Point : Type v} (D : CurveData Input Point)

def Good (A : Input) : Prop := D.Lisse A ∧ D.TameZero A ∧ D.Isoclinic A 1

variable (CR : CurveRules D)

include CR in
theorem good_dual (A : Input) (h : Good D A) : Good D (D.dual A) :=
  ⟨CR.dual_lisse A h.1, CR.dual_tame A h.2.1, CR.dual_isoclinic A 1 h.2.2⟩

include CR in
theorem input_good (A : KloostermanInputData D) : Good D A.input :=
  ⟨A.input_lisse CR, A.input_tame CR, A.input_slope_one CR⟩

variable {C : Type w} [Category.{z} C] [Abelian C]
  {H : CohomologyData Input C} {P : ParameterData C}

/-- Only this conductor-to-lissity law is used by the base-change argument.
In particular, the generic local stage needs no image-purity or sign laws.
Its relative duality and pairing comparisons remain separate inputs. -/
structure CompactLissityRules : Prop where
  compact_lisse : ∀ A, D.Lisse A →
    (∃ N : ℕ, ∀ t, (D.rank A + D.swanZero A t) +
      (D.rank A + D.swanInfinity A t) = N) → P.Lisse (H.compact A)

/-- Existing physical cohomology rules supply the smaller interface. -/
instance : Coe (CohomologyRules D H P) (CompactLissityRules D (H := H) (P := P)) where
  coe G := ⟨G.compact_lisse⟩

variable (G : CompactLissityRules D (H := H) (P := P))

omit [Abelian C] in
include CR G in
/-- The same conductor argument applies to every input in this class,
including the dual, without a family-specific lissity assumption. -/
theorem good_compact_lisse (A : Input) (h : Good D A) : P.Lisse (H.compact A) := by
  apply G.compact_lisse A h.1
  refine ⟨(D.rank A + 0) + (D.rank A + D.rank A), ?_⟩
  intro t
  rw [CR.tame_swan A h.2.1 t, CR.slope_one_swan A h.2.2 t]

variable (DT : Cᵒᵖ ⥤ C)

/-- Canonical relative duality and its compatibility with the compact
pairing, before choosing a correlation or a base change. -/
structure RelativeDuality where
  pairing : ∀ A, H.compact A ⟶ DT.obj (Opposite.op (H.compact (D.dual A)))
  duality : ∀ A, D.Lisse A → D.Isoclinic (D.dual A) 1 →
    P.Lisse (H.compact (D.dual A)) →
    (H.ordinary A ≅ DT.obj (Opposite.op (H.compact (D.dual A))))
  comparison : ∀ A hl hs hc,
    H.comparison A ≫ (duality A hl hs hc).hom = pairing A

variable (S : RelativeDuality D (H := H) (P := P) DT)

def dualityIso (A : Input) (h : Good D A) :
    H.ordinary A ≅ DT.obj (Opposite.op (H.compact (D.dual A))) :=
  S.duality A h.1 (CR.dual_isoclinic A 1 h.2.2)
    (good_compact_lisse D CR G (D.dual A) (good_dual D CR A h))

omit [Abelian C] in
theorem dualityIso_comparison (A : Input) (h : Good D A) :
    H.comparison A ≫ (dualityIso D CR G DT S A h).hom = S.pairing A :=
  S.comparison A _ _ _

variable {Input' : Type a} [Category.{e} Input'] {Point' : Type b}
  {C' : Type c} [Category.{d} C'] [Abelian C']
  (D' : CurveData Input' Point') (CR' : CurveRules D')
  {H' : CohomologyData Input' C'} {P' : ParameterData C'}
  (G' : CompactLissityRules D' (H := H') (P := P')) (DT' : C'ᵒᵖ ⥤ C')
  (S' : RelativeDuality D' (H := H') (P := P') DT')
  (B : C ⥤ C') (pull : Input → Input')

/-- Functoriality of compact cohomology for all target inputs. The
object comparison ties it to the original cohomology record. -/
structure CompactFunctor where
  functor : Input' ⥤ C'
  objectIso : ∀ A, functor.obj A ≅ H'.compact A

def CompactFunctor.mapIso (CF : CompactFunctor (H' := H')) {A B : Input'} (h : A ≅ B) :
    H'.compact A ≅ H'.compact B :=
  (CF.objectIso A).symm ≪≫ CF.functor.mapIso h ≪≫ CF.objectIso B

/-- General compact base change and preservation of fiber properties
for a curve base change. This record has no ordinary-cohomology field. -/
structure CompactBaseChange where
  lisse : ∀ A, D.Lisse A → D'.Lisse (pull A)
  tame : ∀ A, D.TameZero A → D'.TameZero (pull A)
  slope : ∀ A, D.Isoclinic A 1 → D'.Isoclinic (pull A) 1
  dual : ∀ A, D.Lisse A → (pull (D.dual A) ≅ D'.dual (pull A))
  compact : ∀ A, D.Lisse A → (B.obj (H.compact A) ≅ H'.compact (pull A))
  dualTate : ∀ V, P.Lisse V →
    (B.obj (DT.obj (Opposite.op V)) ≅ DT'.obj (Opposite.op (B.obj V)))

variable (CF : CompactFunctor (H' := H'))
  (BC : CompactBaseChange D DT D' DT' B pull (H := H) (H' := H') (P := P))

omit [Abelian C] [Abelian C'] in
include BC in
theorem good_pull (A : Input) (h : Good D A) : Good D' (pull A) :=
  ⟨BC.lisse A h.1, BC.tame A h.2.1, BC.slope A h.2.2⟩

/-- Compact base change for the dual, followed by the canonical
pullback-dual comparison on the original input. -/
def compactDualIso (A : Input) (h : Good D A) :
    B.obj (H.compact (D.dual A)) ≅ H'.compact (D'.dual (pull A)) :=
  BC.compact (D.dual A) (CR.dual_lisse A h.1) ≪≫ CF.mapIso (BC.dual A h.1)

def dualTransportIso (A : Input) (h : Good D A) :
    B.obj (DT.obj (Opposite.op (H.compact (D.dual A)))) ≅
      DT'.obj (Opposite.op (H'.compact (D'.dual (pull A)))) :=
  BC.dualTate (H.compact (D.dual A))
    (good_compact_lisse D CR G (D.dual A) (good_dual D CR A h)) ≪≫
    DT'.mapIso (compactDualIso D CR DT D' DT' B pull CF BC A h).op.symm

/-- Ordinary base change is a constructed comparison, using compact
base change of the dual and the two canonical relative-duality maps. -/
def ordinaryBaseChangeIso (A : Input) (h : Good D A) :
    B.obj (H.ordinary A) ≅ H'.ordinary (pull A) :=
  B.mapIso (dualityIso D CR G DT S A h) ≪≫
    dualTransportIso D CR G DT D' DT' B pull CF BC A h ≪≫
    (dualityIso D' CR' G' DT' S' (pull A) (good_pull D DT D' DT' B pull BC A h)).symm

/-- General naturality of the compact pairing. It contains only compact
cohomology, its pairing and dual transport, not the desired ordinary map. -/
structure CompactPairingBaseChange : Prop where
  natural : ∀ A (h : Good D A),
    (BC.compact A h.1).hom ≫ S'.pairing (pull A) =
      B.map (S.pairing A) ≫ (dualTransportIso D CR G DT D' DT' B pull CF BC A h).hom

omit [Abelian C] [Abelian C'] in
theorem ordinaryBaseChangeIso_duality (A : Input) (h : Good D A) :
    (ordinaryBaseChangeIso D CR G DT S D' CR' G' DT' S' B pull CF BC A h).hom ≫
      (dualityIso D' CR' G' DT' S' (pull A) (good_pull D DT D' DT' B pull BC A h)).hom =
      B.map (dualityIso D CR G DT S A h).hom ≫
        (dualTransportIso D CR G DT D' DT' B pull CF BC A h).hom := by
  simp [ordinaryBaseChangeIso]

variable (PN : CompactPairingBaseChange D CR G DT S D' DT' S' B pull CF BC)

omit [Abelian C] [Abelian C'] in
include PN in
theorem ordinaryBaseChangeIso_comparison (A : Input) (h : Good D A) :
    (BC.compact A h.1).hom ≫ H'.comparison (pull A) =
      B.map (H.comparison A) ≫
        (ordinaryBaseChangeIso D CR G DT S D' CR' G' DT' S' B pull CF BC A h).hom := by
  apply (cancel_mono (dualityIso D' CR' G' DT' S' (pull A)
    (good_pull D DT D' DT' B pull BC A h)).hom).mp
  rw [Category.assoc, dualityIso_comparison, PN.natural, Category.assoc,
    ordinaryBaseChangeIso_duality, ← Category.assoc, ← B.map_comp, dualityIso_comparison]

/-- Restrict the original cohomology operations to the proved admissible
class; no ordinary-base-change statement for arbitrary inputs is needed. -/
def goodCohomology : CohomologyData {A : Input // Good D A} C where
  compact A := H.compact A.val
  ordinary A := H.ordinary A.val
  comparison A := H.comparison A.val

def goodCohomologyBaseChange :
    CohomologyBaseChange (goodCohomology D (H := H)) H' B (fun A => pull A.val) where
  compact A := BC.compact A.val A.property.1
  ordinary A := ordinaryBaseChangeIso D CR G DT S D' CR' G' DT' S' B pull CF BC A.val A.property
  comparison A := ordinaryBaseChangeIso_comparison D CR G DT S D' CR' G' DT' S' B pull CF BC PN
    A.val A.property

variable [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- The original Type III parabolic core now base-changes using only
compact base change, duality and pairing naturality. Its hypotheses of
tameness, slope and compact lissity are derived from its three sources. -/
def inputParabolicBaseChangeIso (A : KloostermanInputData D) :
    B.obj (parabolicCore H A.input) ≅ parabolicCore H' (pull A.input) :=
  parabolicBaseChangeIso (goodCohomology D (H := H)) H' B (fun A => pull A.val)
    (goodCohomologyBaseChange D CR G DT S D' CR' G' DT' S' B pull CF BC PN)
    ⟨A.input, input_good D CR A⟩

end PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality

#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.good_dual
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.input_good
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.good_compact_lisse
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.dualityIso
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.dualityIso_comparison
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.CompactFunctor.mapIso
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.good_pull
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.compactDualIso
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.dualTransportIso
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.ordinaryBaseChangeIso
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.ordinaryBaseChangeIso_duality
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.ordinaryBaseChangeIso_comparison
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.goodCohomologyBaseChange
#print axioms PrimeGap182.TypeIII.OrdinaryBaseChangeFromDuality.inputParabolicBaseChangeIso
