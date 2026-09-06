import Mathlib
import TwinPrime.Basic
import TwinPrime.Sieve.TwinBound

/-!
# Brun's theorem

From the explicit sieve bound `twinCount_le_explicit` with the choice `z = ⌊x^{1/4}⌋` we derive

* `twinCount_le` : `π₂(x) ≤ 2^33 · x / (log x)^2` for all `x ≥ 2`;
* `twinCount_isBigO` : `π₂(x) = O(x / (log x)^2)`;
* `brun` : **Brun's theorem** — the sum of the reciprocals of the twin primes converges,
  in the two forms `Summable (Set.indicator twinPrimes fun n => 1/n)` and
  `Summable (fun p : twinPrimes => 1/p)`.

This is the strongest known upper-bound information about twin primes of this elementary type,
and it is the natural formal counterpart of the fact that twin primes are rare (density zero).
The constant `2^33` is far from optimal; no attempt is made to optimise it.
-/

noncomputable section

open Finset Real Nat
open scoped Topology

namespace TwinPrime

open Sieve

/-! ### Real-analysis helpers -/

theorem log_le_sixteen_mul_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 16 * x ^ (1 / 16 : ℝ) := by
  calc Real.log x ≤ x ^ (1 / 16 : ℝ) / (1 / 16) := Real.log_le_rpow_div hx (by norm_num)
    _ = 16 * x ^ (1 / 16 : ℝ) := by ring

theorem log_pow_eight_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 8 ≤ 2 ^ 32 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  calc (Real.log x) ^ 8 ≤ (16 * x ^ (1 / 16 : ℝ)) ^ 8 :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (log_le_sixteen_mul_rpow hx0) 8
    _ = 16 ^ 8 * (x ^ (1 / 16 : ℝ)) ^ (8 : ℕ) := by rw [mul_pow]
    _ = 2 ^ 32 * x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1 / 16 : ℝ)) 8, ← Real.rpow_mul hx0]
        norm_num
    _ = 2 ^ 32 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]

theorem log_sq_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 2 ^ 8 * x ^ (1 / 8 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  calc (Real.log x) ^ 2 ≤ (16 * x ^ (1 / 16 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (log_le_sixteen_mul_rpow hx0) 2
    _ = 16 ^ 2 * (x ^ (1 / 16 : ℝ)) ^ (2 : ℕ) := by rw [mul_pow]
    _ = 2 ^ 8 * x ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1 / 16 : ℝ)) 2, ← Real.rpow_mul hx0]
        norm_num

/-! ### The parameter `z = ⌊x^{1/4}⌋` -/

/-- Fourth root (floor). -/
def z4 (x : ℕ) : ℕ := Nat.sqrt (Nat.sqrt x)

theorem z4_pow_four_le (x : ℕ) : z4 x ^ 4 ≤ x := by
  unfold z4
  calc Nat.sqrt (Nat.sqrt x) ^ 4 = (Nat.sqrt (Nat.sqrt x) ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt x) ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' _) 2
    _ ≤ x := Nat.sqrt_le' x

theorem lt_z4_add_one_pow_four (x : ℕ) : x < (z4 x + 1) ^ 4 := by
  unfold z4
  have h1 : x < (Nat.sqrt x + 1) ^ 2 := Nat.lt_succ_sqrt' x
  have h2 : Nat.sqrt x < (Nat.sqrt (Nat.sqrt x) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  calc x < (Nat.sqrt x + 1) ^ 2 := h1
    _ ≤ ((Nat.sqrt (Nat.sqrt x) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = (Nat.sqrt (Nat.sqrt x) + 1) ^ 4 := by ring

theorem sixteen_le_z4 {x : ℕ} (hx : 2 ^ 16 ≤ x) : 16 ≤ z4 x := by
  unfold z4
  rw [Nat.le_sqrt]
  rw [Nat.le_sqrt]
  omega

theorem z4_sq_le_sqrt (x : ℕ) : ((z4 x : ℝ)) ^ 2 ≤ Real.sqrt x := by
  unfold z4
  calc ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ^ 2 = ((Nat.sqrt (Nat.sqrt x) ^ 2 : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((Nat.sqrt x : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' _
    _ ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt

/-- `log z ≥ ¼ log x − log 2` for `z = z4 x`, `x ≥ 1`. -/
theorem log_z4_ge {x : ℕ} (hx : 1 ≤ x) :
    (1 / 4 : ℝ) * Real.log x - Real.log 2 ≤ Real.log (z4 x) := by
  have hz1 : 1 ≤ z4 x := by
    unfold z4; rw [Nat.le_sqrt, Nat.le_sqrt]; omega
  have hzpos : (0 : ℝ) < z4 x := by exact_mod_cast hz1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have h1 : Real.log x < 4 * Real.log ((z4 x : ℝ) + 1) := by
    have : Real.log x < Real.log (((z4 x : ℝ) + 1) ^ 4) := by
      apply Real.log_lt_log hxpos
      exact_mod_cast lt_z4_add_one_pow_four x
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2 : Real.log ((z4 x : ℝ) + 1) ≤ Real.log 2 + Real.log (z4 x) := by
    rw [← Real.log_mul (by norm_num) hzpos.ne']
    apply Real.log_le_log (by positivity)
    have : (1 : ℝ) ≤ z4 x := by exact_mod_cast hz1
    linarith
  linarith

/-- `z + 1 ≤ 2 x^{1/4}` for `z = z4 x`. -/
theorem z4_add_one_le {x : ℕ} (hx : 1 ≤ x) :
    ((z4 x : ℝ) + 1) ≤ 2 * (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hz1 : (1 : ℝ) ≤ z4 x := by
    have : 1 ≤ z4 x := by unfold z4; rw [Nat.le_sqrt, Nat.le_sqrt]; omega
    exact_mod_cast this
  have hz : (z4 x : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have h4 : ((z4 x : ℝ) ^ (4 : ℕ)) ≤ (x : ℝ) := by exact_mod_cast z4_pow_four_le x
    calc (z4 x : ℝ) = (((z4 x : ℝ) ^ (4 : ℕ)) ^ ((4 : ℕ) : ℝ)⁻¹) := by
          rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      _ ≤ (x : ℝ) ^ ((4 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow (by positivity) h4 (by positivity)
      _ = (x : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  linarith

/-! ### The bound `π₂(x) ≤ 2^33 x / (log x)^2` -/

/-- For `x ≥ 2^24`: `π₂(x) ≤ 2^33 x / (log x)^2`. -/
theorem twinCount_le_of_large {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    (twinCount x : ℝ) ≤ 2 ^ 33 * x / (Real.log x) ^ 2 := by
  have hx1 : 1 ≤ x := by omega
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hxpos : (0 : ℝ) < x := by linarith
  have hz16 : 16 ≤ z4 x := sixteen_le_z4 (by omega)
  set z := z4 x with hz
  set L := Real.log x with hL
  -- `L ≥ 24 log 2`
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL24 : 24 * Real.log 2 ≤ L := by
    rw [hL, show (24 : ℝ) * Real.log 2 = Real.log (2 ^ 24) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hx)
  have hLpos : 0 < L := by linarith
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ 24 * Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    linarith
  have hmain := twinCount_le_explicit x z hz16
  -- (i) `z + 1 ≤ 2^9 x / L^2`
  have hi : ((z : ℝ) + 1) ≤ 2 ^ 9 * x / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc ((z : ℝ) + 1) * L ^ 2 ≤ (2 * (x : ℝ) ^ (1 / 4 : ℝ)) * (2 ^ 8 * (x : ℝ) ^ (1 / 8 : ℝ)) :=
          mul_le_mul (z4_add_one_le hx1) (log_sq_le hxr) (by positivity) (by positivity)
      _ = 2 ^ 9 * (x : ℝ) ^ (1 / 4 + 1 / 8 : ℝ) := by
          rw [Real.rpow_add hxpos]; ring
      _ ≤ 2 ^ 9 * (x : ℝ) ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hxr (by norm_num))
            (by positivity)
      _ = 2 ^ 9 * x := by rw [Real.rpow_one]
  -- (ii) `(x + 1) / L(z)^2 ≤ 2^11 x / L^2`
  have hLz : L / 32 ≤ Lz z := by
    unfold Lz
    have := log_z4_ge hx1
    rw [← hz] at this
    linarith
  have hLz_pos : 0 < Lz z := Lz_pos hz16
  have hii : ((x : ℝ) + 1) / (Lz z) ^ 2 ≤ 2 ^ 11 * x / L ^ 2 := by
    have hsq : (L / 32) ^ 2 ≤ (Lz z) ^ 2 := pow_le_pow_left₀ (by positivity) hLz 2
    calc ((x : ℝ) + 1) / (Lz z) ^ 2 ≤ ((x : ℝ) + 1) / (L / 32) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = 2 ^ 10 * ((x : ℝ) + 1) / L ^ 2 := by
          field_simp
          ring
      _ ≤ 2 ^ 11 * x / L ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  -- (iii) `z^2 (1 + log z^2)^6 ≤ 2^32 x / L^2`
  have hiii : (z : ℝ) ^ 2 * (1 + Real.log ((z : ℝ) ^ 2)) ^ 6 ≤ 2 ^ 32 * x / L ^ 2 := by
    have hz2 : (z : ℝ) ^ 2 ≤ Real.sqrt x := z4_sq_le_sqrt x
    have hz2pos : (0 : ℝ) < (z : ℝ) ^ 2 := by
      have : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
      positivity
    have hlogz : 1 + Real.log ((z : ℝ) ^ 2) ≤ L := by
      have h1 : Real.log ((z : ℝ) ^ 2) ≤ Real.log (Real.sqrt x) :=
        Real.log_le_log hz2pos hz2
      rw [Real.log_sqrt hxpos.le] at h1
      linarith
    have hlogz_nonneg : 0 ≤ 1 + Real.log ((z : ℝ) ^ 2) := by
      have : 0 ≤ Real.log ((z : ℝ) ^ 2) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
        nlinarith)
      linarith
    rw [le_div_iff₀ (by positivity)]
    calc (z : ℝ) ^ 2 * (1 + Real.log ((z : ℝ) ^ 2)) ^ 6 * L ^ 2
        ≤ Real.sqrt x * L ^ 6 * L ^ 2 := by
          gcongr
      _ = Real.sqrt x * L ^ 8 := by ring
      _ ≤ Real.sqrt x * (2 ^ 32 * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (log_pow_eight_le hxr) (Real.sqrt_nonneg _)
      _ = 2 ^ 32 * x := by
          rw [← mul_assoc, mul_comm (Real.sqrt x), mul_assoc, Real.mul_self_sqrt hxpos.le]
  calc (twinCount x : ℝ) ≤ (z + 1) + ((x : ℝ) + 1) / (Lz z) ^ 2 +
        (z : ℝ) ^ 2 * (1 + Real.log ((z : ℝ) ^ 2)) ^ 6 := hmain
    _ ≤ 2 ^ 9 * x / L ^ 2 + 2 ^ 11 * x / L ^ 2 + 2 ^ 32 * x / L ^ 2 := by
        linarith
    _ = (2 ^ 9 + 2 ^ 11 + 2 ^ 32) * x / L ^ 2 := by ring
    _ ≤ 2 ^ 33 * x / L ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith

/-- **Brun's upper bound.** For all `x ≥ 2`, `π₂(x) ≤ 2^33 x / (log x)^2`. -/
theorem twinCount_le {x : ℕ} (hx : 2 ≤ x) :
    (twinCount x : ℝ) ≤ 2 ^ 33 * x / (Real.log x) ^ 2 := by
  rcases le_or_gt (2 ^ 24) x with h | h
  · exact twinCount_le_of_large h
  · -- small `x`: the trivial bound `π₂(x) ≤ x + 1 ≤ 2 x` and `log x ≤ 24 log 2 ≤ 24`
    have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have htriv : (twinCount x : ℝ) ≤ 2 * x := by
      have : twinCount x ≤ x + 1 := by
        unfold twinCount
        calc #{p ∈ range (x + 1) | p ∈ twinPrimes} ≤ #(range (x + 1)) := card_filter_le _ _
          _ = x + 1 := card_range _
      have : (twinCount x : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hlog : Real.log x ≤ 24 := by
      calc Real.log x ≤ Real.log (2 ^ 24) :=
            Real.log_le_log hxpos (by exact_mod_cast h.le)
        _ = 24 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ ≤ 24 := by
            have : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            linarith
    rw [le_div_iff₀ (by positivity)]
    calc (twinCount x : ℝ) * (Real.log x) ^ 2 ≤ (2 * x) * 24 ^ 2 :=
          mul_le_mul htriv (pow_le_pow_left₀ hlogpos.le hlog 2) (by positivity) (by positivity)
      _ ≤ 2 ^ 33 * x := by nlinarith

/-- `π₂(x) = O(x / (log x)^2)`. -/
theorem twinCount_isBigO :
    (fun x : ℕ => (twinCount x : ℝ)) =O[Filter.atTop] fun x : ℕ => (x : ℝ) / (Real.log x) ^ 2 := by
  apply Asymptotics.IsBigO.of_bound (2 ^ 33)
  rw [Filter.eventually_atTop]
  refine ⟨2, fun x hx => ?_⟩
  have h := twinCount_le hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (twinCount x : ℝ) ≤ 2 ^ 33 * x / (Real.log x) ^ 2 := h
    _ = 2 ^ 33 * ((x : ℝ) / (Real.log x) ^ 2) := by ring

/-! ### Brun's theorem -/

/-- The summand `1/n` on twin primes, `0` elsewhere. -/
def twinRecip (n : ℕ) : ℝ := Set.indicator twinPrimes (fun n : ℕ => (n : ℝ)⁻¹) n

theorem twinRecip_nonneg (n : ℕ) : 0 ≤ twinRecip n := by
  unfold twinRecip
  apply Set.indicator_nonneg
  intro n _
  positivity

theorem twinRecip_zero : twinRecip 0 = 0 := by
  unfold twinRecip
  rw [Set.indicator_of_notMem]
  intro h
  exact Nat.not_prime_zero h.1

/-- Dyadic decomposition of a partial sum. -/
theorem sum_range_two_pow_le (a : ℕ → ℝ) (B : ℕ → ℝ)
    (hblock : ∀ k, ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), a n ≤ B k) (K : ℕ) :
    ∑ n ∈ range (2 ^ K), a n ≤ a 0 + ∑ k ∈ range K, B k := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : 2 ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ K)
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 ^ K)) h1, ← range_eq_Ico,
      sum_range_succ]
    linarith [hblock K]

/-- The block `[2^k, 2^{k+1})` contributes at most `π₂(2^{k+1}) / 2^k`. -/
theorem twinRecip_block_le (k : ℕ) :
    ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinRecip n ≤ (twinCount (2 ^ (k + 1)) : ℝ) / 2 ^ k := by
  classical
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinRecip n
      = ∑ n ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (· ∈ twinPrimes), (n : ℝ)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        unfold twinRecip
        rw [Set.indicator_apply]
    _ ≤ ∑ n ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (· ∈ twinPrimes), ((2 : ℝ) ^ k)⁻¹ := by
        apply sum_le_sum
        intro n hn
        rw [mem_filter, mem_Ico] at hn
        apply inv_anti₀ hpos
        exact_mod_cast hn.1.1
    _ = #((Ico (2 ^ k) (2 ^ (k + 1))).filter (· ∈ twinPrimes)) * ((2 : ℝ) ^ k)⁻¹ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (twinCount (2 ^ (k + 1)) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        unfold twinCount
        apply Nat.cast_le.mpr
        apply card_le_card
        intro n hn
        rw [mem_filter, mem_Ico] at hn
        rw [mem_filter, mem_range]
        exact ⟨by omega, hn.2⟩
    _ = (twinCount (2 ^ (k + 1)) : ℝ) / 2 ^ k := by rw [div_eq_mul_inv]

/-- Each dyadic block is `≤ 2^34 / ((k+1)^2 (log 2)^2)`. -/
theorem twinRecip_block_le' (k : ℕ) :
    ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinRecip n ≤
      2 ^ 34 / (Real.log 2) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := twinRecip_block_le k
  have h2 : (twinCount (2 ^ (k + 1)) : ℝ) ≤
      2 ^ 33 * ((2 : ℝ) ^ (k + 1)) / (Real.log ((2 : ℝ) ^ (k + 1))) ^ 2 := by
    have := twinCount_le (x := 2 ^ (k + 1)) (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right two_pos (by omega))
    push_cast at this
    exact this
  rw [Real.log_pow] at h2
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  calc ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinRecip n
      ≤ (twinCount (2 ^ (k + 1)) : ℝ) / 2 ^ k := h1
    _ ≤ (2 ^ 33 * ((2 : ℝ) ^ (k + 1)) / (((k + 1 : ℕ) : ℝ) * Real.log 2) ^ 2) / 2 ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        push_cast at h2 ⊢
        exact h2
    _ = 2 ^ 34 / (Real.log 2) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        field_simp
        ring

/-- `∑_{k < K} 1/(k+1)^2 ≤ 2`. -/
theorem sum_inv_sq_succ_le (K : ℕ) : ∑ k ∈ range K, (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
  simp only [Nat.cast_zero, zero_add, div_one] at h
  have himg : (range K).image (fun k => k + 1) = Ioo 0 (K + 1) := by
    ext i
    simp only [mem_image, mem_range, mem_Ioo]
    constructor
    · rintro ⟨k, hk, rfl⟩; omega
    · intro hi; exact ⟨i - 1, by omega, by omega⟩
  rw [← himg, sum_image (fun a _ b _ h => Nat.succ_injective h)] at h
  exact h

/-- The partial sums of `twinRecip` are uniformly bounded. -/
theorem sum_twinRecip_le (N : ℕ) :
    ∑ n ∈ range N, twinRecip n ≤ 2 ^ 35 / (Real.log 2) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `N ≤ 2^N`
  have hN : N ≤ 2 ^ N := (Nat.lt_two_pow_self).le
  calc ∑ n ∈ range N, twinRecip n ≤ ∑ n ∈ range (2 ^ N), twinRecip n := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono hN
        · intro n _ _; exact twinRecip_nonneg n
    _ ≤ twinRecip 0 + ∑ k ∈ range N, 2 ^ 34 / (Real.log 2) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
        sum_range_two_pow_le twinRecip _ twinRecip_block_le' N
    _ = 2 ^ 34 / (Real.log 2) ^ 2 * ∑ k ∈ range N, (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [twinRecip_zero, zero_add, mul_sum]
    _ ≤ 2 ^ 34 / (Real.log 2) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_succ_le N) (by positivity)
    _ = 2 ^ 35 / (Real.log 2) ^ 2 := by ring

/-- **Brun's theorem** (indicator form): `∑_{p twin prime} 1/p` converges. -/
theorem brun_summable_indicator :
    Summable (Set.indicator twinPrimes fun n : ℕ => (n : ℝ)⁻¹) :=
  summable_of_sum_range_le twinRecip_nonneg sum_twinRecip_le

/-- **Brun's theorem** (1919): the sum of the reciprocals of the twin primes converges. -/
theorem brun : Summable (fun p : twinPrimes => (1 : ℝ) / p) := by
  have h := brun_summable_indicator
  rw [← summable_subtype_iff_indicator] at h
  refine h.congr fun p => ?_
  simp [one_div]

end TwinPrime
