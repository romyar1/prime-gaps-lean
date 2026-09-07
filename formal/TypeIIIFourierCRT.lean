import TypeIIICRTCounting
import TypeIIIIntervalCompletion

/-!
# Exact Fourier factorization on actual CRT residues

Both residue coordinates and both frequency rescalings are explicit.  This is an identity
for arbitrary functions on coprime residue rings, without an exceptional-set or analytic
input.  It provides the algebraic factorization used before averaging the local masks.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

/-- The product of two local functions evaluated at the actual reductions. -/
def crtTensor (a b : ℕ) [NeZero a] [NeZero b]
    (F : ZMod a → ZMod a → ℂ) (G : ZMod b → ZMod b → ℂ)
    (x y : ZMod (a * b)) : ℂ :=
  F (x.val : ZMod a) (y.val : ZMod a) * G (x.val : ZMod b) (y.val : ZMod b)

theorem chineseRemainder_fst (a b : ℕ) [NeZero a] [NeZero b]
    (hab : a.Coprime b) (z : ZMod (a * b)) :
    (ZMod.chineseRemainder hab z).1 = (z.val : ZMod a) := by
  change (ZMod.cast z : ZMod a × ZMod b).1 = _
  rw [Prod.fst_zmod_cast, ← ZMod.natCast_val]

theorem chineseRemainder_snd (a b : ℕ) [NeZero a] [NeZero b]
    (hab : a.Coprime b) (z : ZMod (a * b)) :
    (ZMod.chineseRemainder hab z).2 = (z.val : ZMod b) := by
  change (ZMod.cast z : ZMod a × ZMod b).2 = _
  rw [Prod.snd_zmod_cast, ← ZMod.natCast_val]

/-- Exact tensor factorization, including the inverse-cofactor frequency factors. -/
theorem fourier₂_crtTensor (a b : ℕ) [NeZero a] [NeZero b]
    (hab : a.Coprime b)
    (F : ZMod a → ZMod a → ℂ) (G : ZMod b → ZMod b → ℂ)
    (H K : ZMod (a * b)) :
    fourier₂ (a * b) (crtTensor a b F G) H K =
      fourier₂ a F ((H.val : ZMod a) * (b : ZMod a)⁻¹)
        ((K.val : ZMod a) * (b : ZMod a)⁻¹) *
      fourier₂ b G ((H.val : ZMod b) * (a : ZMod b)⁻¹)
        ((K.val : ZMod b) * (a : ZMod b)⁻¹) := by
  classical
  let e := ZMod.chineseRemainder hab
  let f (x y : ZMod a) := F x y * ZMod.stdAddChar
    (((e H).1 * (b : ZMod a)⁻¹) * x + ((e K).1 * (b : ZMod a)⁻¹) * y)
  let g (x y : ZMod b) := G x y * ZMod.stdAddChar
    (((e H).2 * (a : ZMod b)⁻¹) * x + ((e K).2 * (a : ZMod b)⁻¹) * y)
  have hterm (x y : ZMod (a * b)) :
      crtTensor a b F G x y * ZMod.stdAddChar (H * x + K * y) =
        f (e x).1 (e y).1 * g (e x).2 (e y).2 := by
    rw [PrimeGap186.stdAddChar_coprime_crt a b hab]
    simp only [crtTensor, map_add, map_mul, Prod.fst_add, Prod.snd_add,
      Prod.fst_mul, Prod.snd_mul, f, g]
    have he₁ (z : ZMod (a * b)) : (e z).1 = (z.val : ZMod a) :=
      chineseRemainder_fst a b hab z
    have he₂ (z : ZMod (a * b)) : (e z).2 = (z.val : ZMod b) :=
      chineseRemainder_snd a b hab z
    simp only [e, chineseRemainder_fst, chineseRemainder_snd]
    rw [show (b : ZMod a)⁻¹ *
        ((H.val : ZMod a) * (x.val : ZMod a) + (K.val : ZMod a) * (y.val : ZMod a)) =
        (H.val : ZMod a) * (b : ZMod a)⁻¹ * (x.val : ZMod a) +
          (K.val : ZMod a) * (b : ZMod a)⁻¹ * (y.val : ZMod a) by ring]
    rw [show (a : ZMod b)⁻¹ *
        ((H.val : ZMod b) * (x.val : ZMod b) + (K.val : ZMod b) * (y.val : ZMod b)) =
        (H.val : ZMod b) * (a : ZMod b)⁻¹ * (x.val : ZMod b) +
          (K.val : ZMod b) * (a : ZMod b)⁻¹ * (y.val : ZMod b) by ring]
    ring
  calc
    _ = ∑ x : ZMod (a * b), ∑ y : ZMod (a * b),
        f (e x).1 (e y).1 * g (e x).2 (e y).2 := by
      simp only [fourier₂, hterm]
    _ = ∑ x : ZMod a × ZMod b, ∑ y : ZMod a × ZMod b,
        f x.1 y.1 * g x.2 y.2 := by
      refine Fintype.sum_equiv e.toEquiv _ _ ?_
      intro x
      refine Fintype.sum_equiv e.toEquiv _ _ ?_
      intro y
      rfl
    _ = (∑ x : ZMod a, ∑ y : ZMod a, f x y) *
        (∑ x : ZMod b, ∑ y : ZMod b, g x y) := by
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by
      simp only [f, g, e, chineseRemainder_fst, chineseRemainder_snd, fourier₂]

/-- Norms factor exactly as well; this is used before any local positive majorant. -/
theorem norm_fourier₂_crtTensor (a b : ℕ) [NeZero a] [NeZero b]
    (hab : a.Coprime b)
    (F : ZMod a → ZMod a → ℂ) (G : ZMod b → ZMod b → ℂ)
    (H K : ZMod (a * b)) :
    ‖fourier₂ (a * b) (crtTensor a b F G) H K‖ =
      ‖fourier₂ a F ((H.val : ZMod a) * (b : ZMod a)⁻¹)
        ((K.val : ZMod a) * (b : ZMod a)⁻¹)‖ *
      ‖fourier₂ b G ((H.val : ZMod b) * (a : ZMod b)⁻¹)
        ((K.val : ZMod b) * (a : ZMod b)⁻¹)‖ := by
  rw [fourier₂_crtTensor a b hab, norm_mul]

#print axioms fourier₂_crtTensor
#print axioms norm_fourier₂_crtTensor

end

end PrimeGap182.TypeIII
