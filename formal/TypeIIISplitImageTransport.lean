import Mathlib.CategoryTheory.Iso

/-!
# Transport of actual split retracts

An isomorphism intertwining two retract projectors restricts to an
isomorphism of their retract objects. The functor is arbitrary:
additivity, exactness, and preservation of images are not required.
-/

namespace PrimeGap182.TypeIII

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  (L : C ⥤ D) {I X : C} {J Y : D}
  (i : I ⟶ X) (r : X ⟶ I) (hi : i ≫ r = 𝟙 I)
  (j : J ⟶ Y) (s : Y ⟶ J) (hj : j ≫ s = 𝟙 J)
  (e : L.obj X ≅ Y)
  (h : L.map (r ≫ i) ≫ e.hom = e.hom ≫ s ≫ j)

/-- Restrict an actual intertwining isomorphism to the two given
split retracts, using their specified inclusions and retractions. -/
def splitRetractTransportIso : L.obj I ≅ J where
  hom := L.map i ≫ e.hom ≫ s
  inv := j ≫ e.inv ≫ L.map r
  hom_inv_id := by
    have hiL : L.map i ≫ L.map r = 𝟙 (L.obj I) := by
      rw [← L.map_comp, hi, L.map_id]
    calc
      _ = L.map i ≫ ((e.hom ≫ s ≫ j) ≫ e.inv) ≫ L.map r := by
        simp only [Category.assoc]
      _ = L.map i ≫ ((L.map (r ≫ i) ≫ e.hom) ≫ e.inv) ≫ L.map r :=
        congrArg (fun g => L.map i ≫ (g ≫ e.inv) ≫ L.map r) h.symm
      _ = (L.map i ≫ L.map r) ≫ (L.map i ≫ L.map r) := by
        simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
      _ = 𝟙 (L.obj I) := by rw [hiL, Category.id_comp]
  inv_hom_id := by
    calc
      _ = j ≫ e.inv ≫ (L.map (r ≫ i) ≫ e.hom) ≫ s := by
        simp only [Functor.map_comp, Category.assoc]
      _ = j ≫ e.inv ≫ (e.hom ≫ s ≫ j) ≫ s :=
        congrArg (fun g => j ≫ e.inv ≫ g ≫ s) h
      _ = (j ≫ s) ≫ (j ≫ s) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = 𝟙 J := by rw [hj, Category.id_comp]

/-- The transport map is the original inclusion, ambient isomorphism,
and target retraction. -/
@[simp]
theorem splitRetractTransportIso_hom :
    (splitRetractTransportIso L i r hi j s hj e h).hom =
      L.map i ≫ e.hom ≫ s := rfl

/-- The inverse transport uses the original target inclusion,
ambient inverse, and source retraction. -/
@[simp]
theorem splitRetractTransportIso_inv :
    (splitRetractTransportIso L i r hi j s hj e h).inv =
      j ≫ e.inv ≫ L.map r := rfl

include hi hj h

/-- The two explicit transport maps compose to the source identity. -/
theorem splitRetractTransportIso_hom_inv_id :
    (L.map i ≫ e.hom ≫ s) ≫ (j ≫ e.inv ≫ L.map r) = 𝟙 (L.obj I) :=
  (splitRetractTransportIso L i r hi j s hj e h).hom_inv_id

/-- The two explicit transport maps compose to the target identity. -/
theorem splitRetractTransportIso_inv_hom_id :
    (j ≫ e.inv ≫ L.map r) ≫ (L.map i ≫ e.hom ≫ s) = 𝟙 J :=
  (splitRetractTransportIso L i r hi j s hj e h).inv_hom_id

#print axioms splitRetractTransportIso
#print axioms splitRetractTransportIso_hom
#print axioms splitRetractTransportIso_inv
#print axioms splitRetractTransportIso_hom_inv_id
#print axioms splitRetractTransportIso_inv_hom_id

end PrimeGap182.TypeIII
