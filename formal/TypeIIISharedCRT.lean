import TypeIIIBaselineBridge

/-!
# The exact three-factor CRT identity in the signed Type III square

The integer Fourier frequency is fixed before the two coprime modulus variables vary.
The two one-sided factors and the shared pair-correlation factor retain their actual
inverse-cofactor scalings. Every assertion here is an identity of finite sums.
-/

open scoped BigOperators Classical

namespace PrimeGap182.TypeIII

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The actual unit Fourier transform of the composite rank-three sum. -/
def singleFourier (q : ℕ) [NeZero q] (A d : ZMod q) : ℂ :=
  ∑ h : (ZMod q)ˣ, PrimeGap186.normalizedKloosterman3Mod q (A * (h : ZMod q)) *
    ZMod.stdAddChar (d * (h : ZMod q))

/-- The actual unit-indexed pair correlation at a composite modulus. -/
def modCorrelation (q : ℕ) [NeZero q] (A B d : ZMod q) : ℂ :=
  ∑ h : (ZMod q)ˣ, PrimeGap186.normalizedKloosterman3Mod q (A * (h : ZMod q)) *
    star (PrimeGap186.normalizedKloosterman3Mod q (B * (h : ZMod q))) *
    ZMod.stdAddChar (d * (h : ZMod q))

theorem modCorrelation_prime (p : ℕ) [Fact p.Prime] (A B d : ZMod p) :
    modCorrelation p A B d = correlation p A B d := by
  simp only [modCorrelation, correlation, kl3_eq_baseline,
    PrimeGap186.normalizedKloosterman3Mod_eq_prime]

/-- The separated Fourier factors have the public, proved square-root bound. -/
theorem singleFourier_norm_le (q : ℕ) [NeZero q] (hq : Squarefree q)
    (A d : ZMod q) (hA : IsUnit A) :
    ‖singleFourier q A d‖ ≤ (3 : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective A
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective d
  exact PrimeGap186.kl3Mod_single_twisted_norm_le q hq a c hA

theorem star_singleFourier_neg (q : ℕ) [NeZero q] (A d : ZMod q) :
    star (singleFourier q A (-d)) =
      ∑ h : (ZMod q)ˣ, star (PrimeGap186.normalizedKloosterman3Mod q (A * (h : ZMod q))) *
        ZMod.stdAddChar (d * (h : ZMod q)) := by
  simp only [singleFourier, star_sum, star_mul, neg_mul, RCLike.star_def,
    ← AddChar.map_neg_eq_conj, neg_neg]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Three independent unit sums, with the reductions taken from the actual CRT residue. -/
theorem sum_units_crt_three (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (huv : u.Coprime v) (huw : u.Coprime w) (hvw : v.Coprime w)
    (f : ZMod u → ℂ) (g : ZMod v → ℂ) (j : ZMod w → ℂ) :
    (∑ h : (ZMod (u * (v * w)))ˣ,
      f ((h : ZMod (u * (v * w))).val : ZMod u) *
        g ((h : ZMod (u * (v * w))).val : ZMod v) *
        j ((h : ZMod (u * (v * w))).val : ZMod w)) =
      (∑ h : (ZMod u)ˣ, f (h : ZMod u)) *
        (∑ h : (ZMod v)ˣ, g (h : ZMod v)) *
        (∑ h : (ZMod w)ˣ, j (h : ZMod w)) := by
  let G (h : ZMod (v * w)) := g (h.val : ZMod v) * j (h.val : ZMod w)
  have hvalv (a : ℕ) : ((a : ZMod (v * w)).val : ZMod v) = (a : ZMod v) :=
    PrimeGap186.cast_val_natCast (v * w) v (dvd_mul_right v w) a
  have hvalw (a : ℕ) : ((a : ZMod (v * w)).val : ZMod w) = (a : ZMod w) :=
    PrimeGap186.cast_val_natCast (v * w) w (dvd_mul_left w v) a
  calc
    _ = ∑ h : (ZMod (u * (v * w)))ˣ,
        f ((h : ZMod (u * (v * w))).val : ZMod u) *
          G ((h : ZMod (u * (v * w))).val : ZMod (v * w)) := by
      simp only [G, hvalv, hvalw, mul_assoc]
    _ = (∑ h : (ZMod u)ˣ, f (h : ZMod u)) *
        (∑ h : (ZMod (v * w))ˣ, G (h : ZMod (v * w))) :=
      PrimeGap186.sum_units_crt u (v * w) (huv.mul_right huw) f G
    _ = _ := by
      rw [show (∑ h : (ZMod (v * w))ˣ, G (h : ZMod (v * w))) =
          (∑ h : (ZMod v)ˣ, g (h : ZMod v)) *
          (∑ h : (ZMod w)ˣ, j (h : ZMod w)) from
        PrimeGap186.sum_units_crt v w hvw g j]
      ring

/-- The periodic product before the common Fourier transform. -/
def sharedPairFunction (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (A B : ℤ) (h : ZMod (u * (v * w))) : ℂ :=
  if IsUnit h then
    PrimeGap186.normalizedKloosterman3Mod (u * w)
      ((A : ZMod (u * w)) * (h.val : ZMod (u * w))) *
    star (PrimeGap186.normalizedKloosterman3Mod (v * w)
      ((B : ZMod (v * w)) * (h.val : ZMod (v * w))))
  else 0

/-- The unnormalized transform at one fixed integer frequency. -/
def sharedPairFourier (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (A B c : ℤ) : ℂ :=
  ∑ h : (ZMod (u * (v * w)))ˣ,
    PrimeGap186.normalizedKloosterman3Mod (u * w)
      ((A : ZMod (u * w)) * ((h : ZMod (u * (v * w))).val : ZMod (u * w))) *
    star (PrimeGap186.normalizedKloosterman3Mod (v * w)
      ((B : ZMod (v * w)) * ((h : ZMod (u * (v * w))).val : ZMod (v * w)))) *
    ZMod.stdAddChar ((c : ZMod (u * (v * w))) * (h : ZMod (u * (v * w))))

/-- The three-factor identity, with the paper's exact inverse cubes and Fourier cofactors. -/
theorem sharedPairFourier_crt (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (huv : u.Coprime v) (huw : u.Coprime w) (hvw : v.Coprime w) (A B c : ℤ) :
    sharedPairFourier u v w A B c =
      singleFourier u ((A : ZMod u) * ((w : ZMod u)⁻¹) ^ 3)
        ((c : ZMod u) * ((v * w : ℕ) : ZMod u)⁻¹) *
      star (singleFourier v ((B : ZMod v) * ((w : ZMod v)⁻¹) ^ 3)
        (-((c : ZMod v) * ((u * w : ℕ) : ZMod v)⁻¹))) *
      modCorrelation w ((A : ZMod w) * ((u : ZMod w)⁻¹) ^ 3)
        ((B : ZMod w) * ((v : ZMod w)⁻¹) ^ 3)
        ((c : ZMod w) * ((u * v : ℕ) : ZMod w)⁻¹) := by
  let f (h : ZMod u) := PrimeGap186.normalizedKloosterman3Mod u
    (((A : ZMod u) * ((w : ZMod u)⁻¹) ^ 3) * h) *
      ZMod.stdAddChar (((c : ZMod u) * ((v * w : ℕ) : ZMod u)⁻¹) * h)
  let g (h : ZMod v) := star (PrimeGap186.normalizedKloosterman3Mod v
    (((B : ZMod v) * ((w : ZMod v)⁻¹) ^ 3) * h)) *
      ZMod.stdAddChar (((c : ZMod v) * ((u * w : ℕ) : ZMod v)⁻¹) * h)
  let j (h : ZMod w) := PrimeGap186.normalizedKloosterman3Mod w
    (((A : ZMod w) * ((u : ZMod w)⁻¹) ^ 3) * h) *
      star (PrimeGap186.normalizedKloosterman3Mod w
        (((B : ZMod w) * ((v : ZMod w)⁻¹) ^ 3) * h)) *
      ZMod.stdAddChar (((c : ZMod w) * ((u * v : ℕ) : ZMod w)⁻¹) * h)
  have hterm (h : ZMod (u * (v * w))) :
      PrimeGap186.normalizedKloosterman3Mod (u * w)
        ((A : ZMod (u * w)) * (h.val : ZMod (u * w))) *
      star (PrimeGap186.normalizedKloosterman3Mod (v * w)
        ((B : ZMod (v * w)) * (h.val : ZMod (v * w)))) *
      ZMod.stdAddChar ((c : ZMod (u * (v * w))) * h) =
        f (h.val : ZMod u) * g (h.val : ZMod v) * j (h.val : ZMod w) := by
    have hchar := PrimeGap186.sourcePhase_stdAddChar_three u v w
      (huv.mul_right huw) hvw (c * (h.val : ℤ))
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at hchar
    rw [PrimeGap186.kloosterman3Mod_int_mul_crt u w huw,
      PrimeGap186.kloosterman3Mod_int_mul_crt v w hvw, hchar, star_mul]
    simp only [PrimeGap186.cast_val_natCast (u * w) u (dvd_mul_right u w),
      PrimeGap186.cast_val_natCast (u * w) w (dvd_mul_left w u),
      PrimeGap186.cast_val_natCast (v * w) v (dvd_mul_right v w),
      PrimeGap186.cast_val_natCast (v * w) w (dvd_mul_left w v), f, g, j]
    rw [show (A : ZMod u) * (h.val : ZMod u) * ((w : ZMod u)⁻¹) ^ 3 =
        ((A : ZMod u) * ((w : ZMod u)⁻¹) ^ 3) * (h.val : ZMod u) by ring,
      show (A : ZMod w) * (h.val : ZMod w) * ((u : ZMod w)⁻¹) ^ 3 =
        ((A : ZMod w) * ((u : ZMod w)⁻¹) ^ 3) * (h.val : ZMod w) by ring,
      show (B : ZMod v) * (h.val : ZMod v) * ((w : ZMod v)⁻¹) ^ 3 =
        ((B : ZMod v) * ((w : ZMod v)⁻¹) ^ 3) * (h.val : ZMod v) by ring,
      show (B : ZMod w) * (h.val : ZMod w) * ((v : ZMod w)⁻¹) ^ 3 =
        ((B : ZMod w) * ((v : ZMod w)⁻¹) ^ 3) * (h.val : ZMod w) by ring,
      show ((v * w : ℕ) : ZMod u)⁻¹ * ((c : ZMod u) * (h.val : ZMod u)) =
        ((c : ZMod u) * ((v * w : ℕ) : ZMod u)⁻¹) * (h.val : ZMod u) by ring,
      show ((u * w : ℕ) : ZMod v)⁻¹ * ((c : ZMod v) * (h.val : ZMod v)) =
        ((c : ZMod v) * ((u * w : ℕ) : ZMod v)⁻¹) * (h.val : ZMod v) by ring,
      show ((u * v : ℕ) : ZMod w)⁻¹ * ((c : ZMod w) * (h.val : ZMod w)) =
        ((c : ZMod w) * ((u * v : ℕ) : ZMod w)⁻¹) * (h.val : ZMod w) by ring]
    ring
  calc
    _ = ∑ h : (ZMod (u * (v * w)))ˣ,
        f ((h : ZMod (u * (v * w))).val : ZMod u) *
          g ((h : ZMod (u * (v * w))).val : ZMod v) *
          j ((h : ZMod (u * (v * w))).val : ZMod w) := by
      simp only [sharedPairFourier, hterm]
    _ = (∑ h : (ZMod u)ˣ, f (h : ZMod u)) *
        (∑ h : (ZMod v)ˣ, g (h : ZMod v)) *
        (∑ h : (ZMod w)ˣ, j (h : ZMod w)) :=
      sum_units_crt_three u v w huv huw hvw f g j
    _ = _ := by rw [star_singleFourier_neg]; rfl

/-- The actual unit sum is the sum over all residues with the unit indicator. -/
theorem sum_units_eq_isUnit_sum (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    (∑ h : (ZMod q)ˣ, F (h : ZMod q)) =
      ∑ x : ZMod q, if IsUnit x then F x else 0 := by
  calc
    _ = ∑ x ∈ Finset.univ.filter IsUnit, F x := by
      apply Finset.sum_bij (fun (h : (ZMod q)ˣ) _ => (h : ZMod q))
      · intro h _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.isUnit⟩
      · intro h _ k _ hk
        exact Units.val_injective hk
      · intro x hx
        obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hx).2
        exact ⟨h, Finset.mem_univ _, rfl⟩
      · intro h _
        rfl
    _ = _ := by rw [Finset.sum_filter]

/-- The shared coefficient is the Fourier transform of the actual periodic unit-masked
product, not an independently stipulated array. -/
theorem sharedPairFourier_eq_transform (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (A B c : ℤ) :
    sharedPairFourier u v w A B c =
      ∑ h : ZMod (u * (v * w)), sharedPairFunction u v w A B h *
        ZMod.stdAddChar ((c : ZMod (u * (v * w))) * h) := by
  let F (h : ZMod (u * (v * w))) :=
    PrimeGap186.normalizedKloosterman3Mod (u * w)
      ((A : ZMod (u * w)) * (h.val : ZMod (u * w))) *
    star (PrimeGap186.normalizedKloosterman3Mod (v * w)
      ((B : ZMod (v * w)) * (h.val : ZMod (v * w)))) *
    ZMod.stdAddChar ((c : ZMod (u * (v * w))) * h)
  have hh := sum_units_eq_isUnit_sum (u * (v * w)) F
  simpa only [F, sharedPairFourier, sharedPairFunction, ite_mul, zero_mul] using hh

/-- The exact Fourier coefficient with the inverse row and column indices used in the
signed second moment. The integer representatives are taken at their own moduli. -/
def sharedInverseFourier (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a m n c : ℤ) : ℂ :=
  sharedPairFourier u v w
    (((a : ZMod (u * w)) * (m : ZMod (u * w))⁻¹).val : ℤ)
    (((a : ZMod (v * w)) * (n : ZMod (v * w))⁻¹).val : ℤ) c

theorem sharedInverseFourier_eq (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (a m n c : ℤ) :
    sharedInverseFourier u v w a m n c =
      ∑ h : (ZMod (u * (v * w)))ˣ,
        PrimeGap186.normalizedKloosterman3Mod (u * w)
          (((a : ZMod (u * w)) * (m : ZMod (u * w))⁻¹) *
            ((h : ZMod (u * (v * w))).val : ZMod (u * w))) *
        star (PrimeGap186.normalizedKloosterman3Mod (v * w)
          (((a : ZMod (v * w)) * (n : ZMod (v * w))⁻¹) *
            ((h : ZMod (u * (v * w))).val : ZMod (v * w)))) *
        ZMod.stdAddChar ((c : ZMod (u * (v * w))) * (h : ZMod (u * (v * w)))) := by
  simp only [sharedInverseFourier, sharedPairFourier, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Reduction of an actual inverse index through a divisor modulus. -/
theorem inverse_index_val_reduce (q d : ℕ) [NeZero q] (hd : d ∣ q)
    (a m : ℤ) (hm : IsUnit (m : ZMod q)) :
    ((((a : ZMod q) * (m : ZMod q)⁻¹).val : ℤ) : ZMod d) =
      (a : ZMod d) * (m : ZMod d)⁻¹ := by
  let π := ZMod.castHom hd (ZMod d)
  calc
    _ = π ((a : ZMod q) * (m : ZMod q)⁻¹) := by
      simp only [π, ZMod.castHom_apply, ZMod.cast_eq_val, Int.cast_natCast]
    _ = _ := by
      rw [map_mul, map_intCast, PrimeGap186.phaseCRT_map_inv π hm, map_intCast]

/-- The exact CRT factorization for inverse indices, under only their actual unit guards. -/
theorem sharedInverseFourier_crt (u v w : ℕ) [NeZero u] [NeZero v] [NeZero w]
    (huv : u.Coprime v) (huw : u.Coprime w) (hvw : v.Coprime w) (a m n c : ℤ)
    (hm : IsUnit (m : ZMod (u * w))) (hn : IsUnit (n : ZMod (v * w))) :
    sharedInverseFourier u v w a m n c =
      singleFourier u ((a : ZMod u) * (m : ZMod u)⁻¹ * ((w : ZMod u)⁻¹) ^ 3)
        ((c : ZMod u) * ((v * w : ℕ) : ZMod u)⁻¹) *
      star (singleFourier v ((a : ZMod v) * (n : ZMod v)⁻¹ * ((w : ZMod v)⁻¹) ^ 3)
        (-((c : ZMod v) * ((u * w : ℕ) : ZMod v)⁻¹))) *
      modCorrelation w ((a : ZMod w) * (m : ZMod w)⁻¹ * ((u : ZMod w)⁻¹) ^ 3)
        ((a : ZMod w) * (n : ZMod w)⁻¹ * ((v : ZMod w)⁻¹) ^ 3)
        ((c : ZMod w) * ((u * v : ℕ) : ZMod w)⁻¹) := by
  rw [sharedInverseFourier, sharedPairFourier_crt u v w huv huw hvw,
    inverse_index_val_reduce (u * w) u (dvd_mul_right u w) a m hm,
    inverse_index_val_reduce (u * w) w (dvd_mul_left w u) a m hm,
    inverse_index_val_reduce (v * w) v (dvd_mul_right v w) a n hn,
    inverse_index_val_reduce (v * w) w (dvd_mul_left w v) a n hn]

#print axioms singleFourier_norm_le
#print axioms sum_units_crt_three
#print axioms sharedPairFourier_crt
#print axioms sharedPairFourier_eq_transform
#print axioms sharedInverseFourier_crt

end

end PrimeGap182.TypeIII
