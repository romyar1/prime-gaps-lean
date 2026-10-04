import TypeIIIOriginStalksFromStandardWeilInvariants01

/-! A chosen finite-extension Frobenius lift may map to inertia times a power
of a base-field lift. On the invariant stalk the inertia factor disappears.
These are pure consequences of the SAME Weil action and its finite-dimensional
invariant action, without a normal-form premise or a claim that the finite-field
Weil map, cross-field comparison, or native model has been constructed. -/
noncomputable section
open CategoryTheory
namespace PrimeGap182.TypeIII.OriginFrobeniusPowerFromInertiaTwistedLift
open LocalWeilAction OriginStalksFromStandardWeilInvariants
universe u v g
variable {Line : Type u} [Category.{v} Line] {G : Type g} [Group G]
  (J : Line ⥤ FDRep ℂ G) (phi : G →* G) (W : LocalWeilAction.Data J phi)

theorem representation_frobenius_pow (A : Line) (n : ℕ)
    (x : Representation.invariants (J.obj A).ρ) :
    W.representation A (W.frobenius ^ n) x.val =
      (((invariantStalks J phi W).frobenius A ^ n) x).val := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero, map_one, pow_zero]
      rfl
  | succ n ih =>
      rw [pow_succ, map_mul, pow_succ]
      change W.representation A (W.frobenius ^ n)
        (W.localFrobenius.action A x.val) =
          (((invariantStalks J phi W).frobenius A ^ n)
            ((invariantStalks J phi W).frobenius A x)).val
      exact ih ((invariantStalks J phi W).frobenius A x)

theorem representation_inertia_frobenius_pow (A : Line) (q : G) (n : ℕ)
    (x : Representation.invariants (J.obj A).ρ) :
    W.representation A (W.inertia q * W.frobenius ^ n) x.val =
      (((invariantStalks J phi W).frobenius A ^ n) x).val := by
  rw [map_mul, W.restriction]
  change (J.obj A).ρ q (W.representation A (W.frobenius ^ n) x.val) = _
  rw [representation_frobenius_pow]
  exact (((invariantStalks J phi W).frobenius A ^ n) x).property q

theorem representation_frobenius_pow_inertia (A : Line) (q : G) (n : ℕ)
    (x : Representation.invariants (J.obj A).ρ) :
    W.representation A (W.frobenius ^ n * W.inertia q) x.val =
      (((invariantStalks J phi W).frobenius A ^ n) x).val := by
  rw [map_mul, W.restriction]
  change W.representation A (W.frobenius ^ n) ((J.obj A).ρ q x.val) = _
  rw [x.property q]
  exact representation_frobenius_pow J phi W A n x

end PrimeGap182.TypeIII.OriginFrobeniusPowerFromInertiaTwistedLift
