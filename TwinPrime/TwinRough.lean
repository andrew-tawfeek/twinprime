import Mathlib
import TwinPrime.Sieve.Legendre
import TwinPrime.Brun
import TwinPrime.Conditional

/-!
# Infinitely many twin rough numbers

With the sifting level `z(x) = ⌊log x / (2 log 3)⌋`, Legendre's sieve (`twinRough_count_ge`)
gives, for `x ≥ 2^24`,

  `#{n ≤ x : n(n+2) has no prime factor ≤ z(x)} ≥ x / (log x)²`

(`twinRough_count_ge_of_large`), hence (`twinRough_infinite`): **there are infinitely many `n`
such that every prime factor of `n (n + 2)` exceeds `log n / (2 log 3)`** — both `n` and `n + 2`
are simultaneously "rough".  This is the first lower-bound result of twin type in the library.
-/

noncomputable section

open Finset Real Filter Topology
open TwinPrime.Sieve

namespace TwinPrime

/-- The sifting level `z(x) = ⌊log x / (2 log 3)⌋`. -/
def zL (x : ℕ) : ℕ := ⌊Real.log x / (2 * Real.log 3)⌋₊

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem zL_le {x : ℕ} : (zL x : ℝ) ≤ Real.log x / (2 * Real.log 3) := by
  unfold zL
  apply Nat.floor_le
  have h0 : 0 ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
  positivity

theorem three_le_zL {x : ℕ} (hx : 3 ^ 6 ≤ x) : 3 ≤ zL x := by
  unfold zL
  apply Nat.le_floor
  have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
  rw [le_div_iff₀ (by positivity)]
  have : Real.log ((3 : ℝ) ^ 6) ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  rw [Real.log_pow] at this
  push_cast at this ⊢
  linarith

/-- `3^{z(x)+1} ≤ 3 √x`. -/
theorem three_pow_zL_le {x : ℕ} (hx : 1 ≤ x) : (3 : ℝ) ^ (zL x + 1) ≤ 3 * Real.sqrt x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
  have h1 : (3 : ℝ) ^ (zL x) ≤ Real.sqrt x := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    calc Real.log 3 * (zL x : ℝ) ≤ Real.log 3 * (Real.log x / (2 * Real.log 3)) :=
          mul_le_mul_of_nonneg_left zL_le hlog3.le
      _ = Real.log x * (1 / 2) := by field_simp
  calc (3 : ℝ) ^ (zL x + 1) = 3 * 3 ^ (zL x) := by ring
    _ ≤ 3 * Real.sqrt x := by linarith

/-- `√x (log x)² ≤ x / 2` for `x ≥ 2^24`. -/
theorem sqrt_mul_log_sq_le {x : ℝ} (hx : 2 ^ 24 ≤ x) : Real.sqrt x * (Real.log x) ^ 2 ≤ x / 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog := log_sq_le hx1                      -- (log x)^2 ≤ 2^8 x^{1/8}
  have h58 : Real.sqrt x * x ^ (1 / 8 : ℝ) = x ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
    norm_num
  have h38 : (512 : ℝ) ≤ x ^ (3 / 8 : ℝ) := by
    have : ((2 : ℝ) ^ (24 : ℕ)) ^ (3 / 8 : ℝ) = 2 ^ (9 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      norm_num
    calc (512 : ℝ) = ((2 : ℝ) ^ (24 : ℕ)) ^ (3 / 8 : ℝ) := by rw [this]; norm_num
      _ ≤ x ^ (3 / 8 : ℝ) := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)
  have hsplit : x = x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have h58pos : 0 ≤ x ^ (5 / 8 : ℝ) := by positivity
  calc Real.sqrt x * (Real.log x) ^ 2 ≤ Real.sqrt x * (2 ^ 8 * x ^ (1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)
    _ = 2 ^ 8 * x ^ (5 / 8 : ℝ) := by rw [← h58]; ring
    _ = 2 ^ 8 * x ^ (5 / 8 : ℝ) * 512 / 512 := by ring
    _ ≤ 2 ^ 8 * x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) / 512 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_left h38 (by positivity)
    _ = x / 2 := by rw [mul_assoc, ← hsplit]; ring

/-- For `x ≥ 2^24`: `#{n ≤ x : n(n+2) coprime to primorial z(x)} ≥ x / (log x)²`. -/
theorem twinRough_count_ge_of_large {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    (x : ℝ) / (Real.log x) ^ 2 ≤
      (#{n ∈ range (x + 1) | Nat.Coprime (primorial (zL x)) (n * (n + 2))} : ℝ) := by
  have hx1 : 1 ≤ x := by omega
  have hxr : (2 : ℝ) ^ 24 ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hz3 : 3 ≤ zL x := three_le_zL (by omega)
  have hlog3 := one_le_log_three
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  refine le_trans ?_ (twinRough_count_ge x (zL x) hz3)
  have hz_le : (zL x : ℝ) ≤ Real.log x / (2 * Real.log 3) := zL_le
  have hzpos : (0 : ℝ) < zL x := by exact_mod_cast (by omega : 0 < zL x)
  -- (x+1)/z² ≥ (x+1) (2 log 3)² / (log x)² ≥ 4 (x+1)/(log x)²
  have h1 : ((x : ℝ) + 1) * 4 / (Real.log x) ^ 2 ≤ ((x : ℝ) + 1) / (zL x : ℝ) ^ 2 := by
    have hsq : (zL x : ℝ) ^ 2 ≤ (Real.log x / (2 * Real.log 3)) ^ 2 :=
      pow_le_pow_left₀ hzpos.le hz_le 2
    have h4 : (Real.log x / (2 * Real.log 3)) ^ 2 ≤ (Real.log x) ^ 2 / 4 := by
      rw [div_pow]
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      nlinarith
    calc ((x : ℝ) + 1) * 4 / (Real.log x) ^ 2 = ((x : ℝ) + 1) / ((Real.log x) ^ 2 / 4) := by
          field_simp
      _ ≤ ((x : ℝ) + 1) / (zL x : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (le_trans hsq h4)
  -- 3^{z+1} ≤ 3 √x ≤ (3/2) x / (log x)²
  have h2 : (3 : ℝ) ^ (zL x + 1) ≤ 3 / 2 * x / (Real.log x) ^ 2 := by
    calc (3 : ℝ) ^ (zL x + 1) ≤ 3 * Real.sqrt x := three_pow_zL_le hx1
      _ ≤ 3 / 2 * x / (Real.log x) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          have := sqrt_mul_log_sq_le hxr
          linarith
  have h3 : (x : ℝ) / (Real.log x) ^ 2 ≤ ((x : ℝ) + 1) * 4 / (Real.log x) ^ 2 -
      3 / 2 * x / (Real.log x) ^ 2 := by
    rw [div_sub_div_same, div_le_div_iff_of_pos_right (by positivity)]
    linarith
  linarith

/-- **Twin rough numbers.** There are infinitely many `n` such that every prime factor of
`n (n + 2)` exceeds `log n / (2 log 3)`; equivalently, `n` and `n + 2` simultaneously have no
prime factor `≤ log n / (2 log 3)`. -/
theorem twinRough_infinite :
    {n : ℕ | ∀ p, p.Prime → p ∣ n * (n + 2) → Real.log n / (2 * Real.log 3) < p}.Infinite := by
  set S := {n : ℕ | ∀ p, p.Prime → p ∣ n * (n + 2) → Real.log n / (2 * Real.log 3) < p} with hS
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- the sifted set at level `x` is contained in `S`
  have hsub : ∀ x : ℕ, 1 ≤ x →
      {n ∈ range (x + 1) | Nat.Coprime (primorial (zL x)) (n * (n + 2))} ⊆ hfin.toFinset := by
    intro x hx n hn
    rw [mem_filter, mem_range] at hn
    rw [Set.Finite.mem_toFinset, hS, Set.mem_setOf_eq]
    intro p hp hpn
    have hpz : zL x < p := by
      by_contra h
      exact (coprime_primorial_iff.mp hn.2) p hp (by omega) hpn
    have hlog : Real.log n ≤ Real.log x := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hx)
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : n ≤ x))
    have hlog3 : 0 < Real.log 3 := by linarith [one_le_log_three]
    calc Real.log n / (2 * Real.log 3) ≤ Real.log x / (2 * Real.log 3) :=
          div_le_div_of_nonneg_right hlog (by positivity)
      _ < (zL x : ℝ) + 1 := by
          unfold zL
          exact Nat.lt_floor_add_one _
      _ ≤ p := by exact_mod_cast hpz
  -- so the sifted counts are bounded, contradicting `x/(log x)² → ∞`
  have hbound : ∀ x : ℕ, 2 ^ 24 ≤ x → (x : ℝ) / (Real.log x) ^ 2 ≤ hfin.toFinset.card := by
    intro x hx
    calc (x : ℝ) / (Real.log x) ^ 2
        ≤ (#{n ∈ range (x + 1) | Nat.Coprime (primorial (zL x)) (n * (n + 2))} : ℝ) :=
          twinRough_count_ge_of_large hx
      _ ≤ hfin.toFinset.card := by exact_mod_cast card_le_card (hsub x (by omega))
  have htend : Tendsto (fun x : ℕ => (x : ℝ) / (Real.log x) ^ 2) atTop atTop :=
    tendsto_div_log_sq_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨x, hx1, hx2⟩ := ((tendsto_atTop.mp htend (hfin.toFinset.card + 1)).and
    (eventually_ge_atTop (2 ^ 24))).exists
  have := hbound x hx2
  have hx1' : (hfin.toFinset.card : ℝ) + 1 ≤ (x : ℝ) / (Real.log x) ^ 2 := hx1
  linarith

end TwinPrime
