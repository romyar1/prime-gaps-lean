import TypeIIINaturalCompactBaseChange

/-!
# Compact-pairing base change from cup product, evaluation and trace

The pairing is tested against the same dual evaluation. Its bilinear form
is the actual degree-two cup product, followed by the image of the source
evaluation and the trace. General functoriality and base-change laws for
these operations remain published inputs; the compact-pairing square is
derived, not supplied. No ordinary base-change premise is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace PrimeGap182.TypeIII.CompactPairingFromCupTrace

universe u v w z a b c d e k
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (DT : Cᵒᵖ ⥤ C) (Lisse : C → Prop)

/-- General dual/Tate evaluation; faithfulness is needed only on lisse
objects. The trace line is the same one used by compact cohomology. -/
structure Evaluation where
  line : C
  evaluate : ∀ V, V ⊗ DT.obj (Opposite.op V) ⟶ line
  natural : ∀ {V W} (f : V ⟶ W),
    (f ⊗ₘ 𝟙 (DT.obj (Opposite.op W))) ≫ evaluate W =
      (𝟙 V ⊗ₘ DT.map f.op) ≫ evaluate V
  separates : ∀ V, Lisse V → ∀ U (f g : U ⟶ DT.obj (Opposite.op V)),
    (𝟙 V ⊗ₘ f) ≫ evaluate V = (𝟙 V ⊗ₘ g) ≫ evaluate V → f = g

variable {DT Lisse} (E : Evaluation DT Lisse)

theorem Evaluation.transport {V W : C} (j : V ≅ W) :
    (j.hom ⊗ₘ (DT.mapIso j.op.symm).hom) ≫ E.evaluate W = E.evaluate V := by
  have hn := E.natural j.inv
  have h := congrArg (fun f => (j.hom ⊗ₘ 𝟙 (DT.obj (Opposite.op V))) ≫ f) hn
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Iso.hom_inv_id, CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id] at h
  simpa using h.symm


/-- Evaluation turns transport through a dual isomorphism into transport
of its argument; no nondegeneracy assertion is used in this identity. -/
theorem Evaluation.transport_map {U V W : C} (j : V ≅ W)
    (f : U ⟶ DT.obj (Opposite.op V)) :
    (j.hom ⊗ₘ (f ≫ (DT.mapIso j.op.symm).hom)) ≫ E.evaluate W =
      (𝟙 V ⊗ₘ f) ≫ E.evaluate V := by
  have h := congrArg (fun k => (𝟙 V ⊗ₘ f) ≫ k) (E.transport j)
  simpa only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.Category.id_comp] using h

variable {Input : Type w} [Category.{z} Input] [MonoidalCategory Input]
  (H K : Input ⥤ C) (dual : Input → Input)
  (ev : ∀ A, dual A ⊗ A ⟶ 𝟙_ Input) (L : Input → Prop)
  (pairing : ∀ A, H.obj A ⟶ DT.obj (Opposite.op (H.obj (dual A))))

/-- Degree-one cup product and degree-two trace on the original functors.
The identification is the usual cup/evaluation/trace definition of the
relative-duality pairing after forgetting compact supports. -/
structure Data where
  cup : ∀ A V, H.obj A ⊗ H.obj V ⟶ K.obj (A ⊗ V)
  natural : ∀ {A A' V V'} (f : A ⟶ A') (g : V ⟶ V'),
    (H.map f ⊗ₘ H.map g) ≫ cup A' V' = cup A V ≫ K.map (f ⊗ₘ g)
  trace : K.obj (𝟙_ Input) ⟶ E.line
  formula : ∀ A, L A → (𝟙 (H.obj (dual A)) ⊗ₘ pairing A) ≫ E.evaluate (H.obj (dual A)) =
    cup (dual A) A ≫ K.map (ev A) ≫ trace

variable {E H K dual ev L pairing} (T : Data E H K dual ev L pairing)

def Data.form (A : Input) : H.obj (dual A) ⊗ H.obj A ⟶ E.line :=
  T.cup (dual A) A ≫ K.map (ev A) ≫ T.trace

variable {Input' : Type a} [Category.{b} Input'] [MonoidalCategory Input']
  {C' : Type c} [Category.{d} C'] [MonoidalCategory C']
  {DT' : C'ᵒᵖ ⥤ C'} {Lisse' : C' → Prop} (E' : Evaluation DT' Lisse')
  {H' K' : Input' ⥤ C'} {dual' : Input' → Input'}
  {ev' : ∀ A, dual' A ⊗ A ⟶ 𝟙_ Input'} {L' : Input' → Prop}
  {pairing' : ∀ A, H'.obj A ⟶ DT'.obj (Opposite.op (H'.obj (dual' A)))}
  (T' : Data E' H' K' dual' ev' L' pairing')
  (B : C ⥤ C') [B.Monoidal] (pull : Input ⥤ Input') [pull.Monoidal]
  (compact : H ⋙ B ≅ pull ⋙ H')
  (dualPull : ∀ A, L A → (pull.obj (dual A) ≅ dual' (pull.obj A)))
  (dualTate : ∀ V, Lisse V → (B.obj (DT.obj (Opposite.op V)) ≅
    DT'.obj (Opposite.op (B.obj V))))

variable {E'}

/-- General cup, trace, source evaluation and dual evaluation base change.
The degree-two comparison is natural on all original coefficient maps.
These clauses contain no compact-pairing or ordinary-cohomology square. -/
structure BaseChange where
  top : K ⋙ B ≅ pull ⋙ K'
  line : B.obj E.line ≅ E'.line
  cup : ∀ A V,
    ((compact.app A).hom ⊗ₘ (compact.app V).hom) ≫ T'.cup (pull.obj A) (pull.obj V) =
      Functor.LaxMonoidal.μ B (H.obj A) (H.obj V) ≫ B.map (T.cup A V) ≫
        (top.app (A ⊗ V)).hom ≫ K'.map (Functor.Monoidal.μIso pull A V).inv
  trace : (top.app (𝟙_ Input)).hom ≫ K'.map (Functor.Monoidal.εIso pull).inv ≫ T'.trace =
    B.map T.trace ≫ line.hom
  sourceEvaluation : ∀ A (hA : L A),
    ((dualPull A hA).hom ⊗ₘ 𝟙 (pull.obj A)) ≫ ev' (pull.obj A) =
      (Functor.Monoidal.μIso pull (dual A) A).hom ≫
        pull.map (ev A) ≫ (Functor.Monoidal.εIso pull).inv
  dualEvaluation : ∀ V (hV : Lisse V),
    (𝟙 (B.obj V) ⊗ₘ (dualTate V hV).hom) ≫ E'.evaluate (B.obj V) =
      Functor.LaxMonoidal.μ B V (DT.obj (Opposite.op V)) ≫
        B.map (E.evaluate V) ≫ line.hom

variable {T T' B pull compact dualPull dualTate}
  (M : BaseChange T T' B pull compact dualPull dualTate)

/-- Cup functoriality moves the exact curve-dual comparison inside the
original degree-two functor. Base change then commutes with evaluation
and trace on that functor. -/
theorem BaseChange.form (A : Input) (hA : L A) :
    (((compact.app (dual A)).hom ≫ H'.map (dualPull A hA).hom) ⊗ₘ
      (compact.app A).hom) ≫ T'.form (pull.obj A) =
    Functor.LaxMonoidal.μ B (H.obj (dual A)) (H.obj A) ≫
      B.map (T.form A) ≫ M.line.hom := by
  unfold Data.form
  have hn := T'.natural (dualPull A hA).hom (𝟙 (pull.obj A))
  simp only [CategoryTheory.Functor.map_id] at hn
  rw [show ((compact.app (dual A)).hom ≫ H'.map (dualPull A hA).hom) ⊗ₘ
      (compact.app A).hom =
      ((compact.app (dual A)).hom ⊗ₘ (compact.app A).hom) ≫
        (H'.map (dualPull A hA).hom ⊗ₘ 𝟙 (H'.obj (pull.obj A))) by
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      exact congrArg (fun k => ((compact.app (dual A)).hom ≫
        H'.map (dualPull A hA).hom) ⊗ₘ k) (Category.comp_id (compact.app A).hom).symm]
  simp only [Category.assoc]
  rw [← Category.assoc _ (T'.cup _ _), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (K'.map _) (K'.map _), ← CategoryTheory.Functor.map_comp, M.sourceEvaluation]
  rw [← Category.assoc _ (T'.cup _ _), M.cup]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc (K'.map _) (K'.map _), ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp]
  have ht : B.map (K.map (ev A)) ≫ (M.top.app (𝟙_ Input)).hom =
      (M.top.app (dual A ⊗ A)).hom ≫ K'.map (pull.map (ev A)) :=
    M.top.hom.naturality (ev A)
  rw [← Category.assoc (M.top.app _).hom (K'.map _), ← ht]
  simp only [Category.assoc]
  rw [M.trace]


include M in
/-- Equality of the cup/evaluation/trace forms determines the original
compact pairing. The lisse guards apply only where dual evaluation is
used faithfully and where its base-change comparison is available. -/
theorem BaseChange.compatibility (A : Input) (hA : L A) (hA' : L' (pull.obj A))
    (hV : Lisse (H.obj (dual A)))
    (hV' : Lisse' (H'.obj (dual' (pull.obj A)))) :
    (compact.app A).hom ≫ pairing' (pull.obj A) =
      B.map (pairing A) ≫ (dualTate (H.obj (dual A)) hV).hom ≫
        (DT'.mapIso ((compact.app (dual A)) ≪≫ H'.mapIso (dualPull A hA)).op.symm).hom := by
  let j := (compact.app (dual A)) ≪≫ H'.mapIso (dualPull A hA)
  apply E'.separates _ hV'
  apply (cancel_epi (j.hom ⊗ₘ 𝟙 (B.obj (H.obj A)))).mp
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]
  have left : (j.hom ⊗ₘ ((compact.app A).hom ≫ pairing' (pull.obj A))) ≫
      E'.evaluate (H'.obj (dual' (pull.obj A))) =
      Functor.LaxMonoidal.μ B (H.obj (dual A)) (H.obj A) ≫
        B.map (T.form A) ≫ M.line.hom := by
    have hf := congrArg (fun f => (j.hom ⊗ₘ (compact.app A).hom) ≫ f)
      (T'.formula (pull.obj A) hA')
    simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id] at hf
    apply hf.trans
    simpa [Data.form, j, Category.assoc] using M.form A hA
  rw [left]
  have hr := E'.transport_map j (B.map (pairing A) ≫ (dualTate (H.obj (dual A)) hV).hom)
  rw [hr]
  dsimp only [CategoryTheory.Functor.comp_obj]
  have ht := congrArg (fun f => (𝟙 (B.obj (H.obj (dual A))) ⊗ₘ B.map (pairing A)) ≫ f)
    (M.dualEvaluation (H.obj (dual A)) hV)
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.Category.id_comp] at ht
  rw [ht]
  have hn := Functor.LaxMonoidal.μ_natural B (𝟙 (H.obj (dual A))) (pairing A)
  simp only [CategoryTheory.Functor.map_id] at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← Category.assoc (B.map _) (B.map _), ← CategoryTheory.Functor.map_comp,
    T.formula A hA]
  rfl

end PrimeGap182.TypeIII.CompactPairingFromCupTrace

#print axioms PrimeGap182.TypeIII.CompactPairingFromCupTrace.Evaluation.transport
#print axioms PrimeGap182.TypeIII.CompactPairingFromCupTrace.Evaluation.transport_map
#print axioms PrimeGap182.TypeIII.CompactPairingFromCupTrace.Data.form
#print axioms PrimeGap182.TypeIII.CompactPairingFromCupTrace.BaseChange.form
#print axioms PrimeGap182.TypeIII.CompactPairingFromCupTrace.BaseChange.compatibility
