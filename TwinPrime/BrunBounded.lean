import Mathlib
import TwinPrime.Sieve.BrunFinal
import TwinPrime.BrunAlmostPrime

/-!
# Brun's theorem: twin almost-primes with a bounded number of prime factors

With `z(x) = ⌊x^{1/2000}⌋` in `brunHooley_twin_count_ge`, the remainder is `≤ √x` and the main
term is `≥ x^{0.9}` for large `x`, so

  `#{n ≤ x : n(n+2) has no prime factor ≤ x^{1/2000}} ≥ x^{0.8}`   (`brunBounded_count_ge`).

Every such `n` has `Ω(n) + Ω(n+2) = Ω(n(n+2)) ≤ 2 log(x+2)/log(z+1) ≤ 4001`.  Hence
(`brun_bounded_infinite`): **there are infinitely many `n` such that `n` and `n + 2` together
have at most `4001` prime factors** (counted with multiplicity).  This is Brun's 1920 theorem in
kind (Brun: `9 + 9`); the constant `4001` reflects the crude Mertens bound and unoptimised
parameters, not the method.
-/

noncomputable section

open Finset Real Filter Topology
open TwinPrime.Sieve
open scoped ArithmeticFunction.Omega

namespace TwinPrime

/-- The sifting level `z(x) = ⌊x^{1/2000}⌋`. -/
def zC (x : ℕ) : ℕ := ⌊(x : ℝ) ^ (1 / 2000 : ℝ)⌋₊

theorem zC_le_rpow (x : ℕ) : (zC x : ℝ) ≤ (x : ℝ) ^ (1 / 2000 : ℝ) :=
  Nat.floor_le (by positivity)

theorem rpow_lt_zC_add_one (x : ℕ) : (x : ℝ) ^ (1 / 2000 : ℝ) < (zC x : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem zC_le_self {x : ℕ} (hx : 1 ≤ x) : zC x ≤ x := by
  have h1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have : (x : ℝ) ^ (1 / 2000 : ℝ) ≤ x := by
    calc (x : ℝ) ^ (1 / 2000 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = x := Real.rpow_one _
  exact_mod_cast le_trans (zC_le_rpow x) this

/-! ### The number of blocks is `O(log log x)` -/

/-- `Nat.log 2 y ≤ log y / log 2`. -/
theorem natLog_le_log_div {y : ℕ} (hy : 1 ≤ y) :
    (Nat.log 2 y : ℝ) ≤ Real.log y / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  have h := Nat.pow_log_le_self 2 (by omega : y ≠ 0)
  have : Real.log ((2 : ℝ) ^ Nat.log 2 y) ≤ Real.log y :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  rw [Real.log_pow] at this
  exact this

/-- `nBlocks (zC x) ≤ 2 log log x + 3` for `x ≥ 16`. -/
theorem nBlocks_zC_le {x : ℕ} (hx : 16 ≤ x) :
    (nBlocks (zC x) : ℝ) ≤ 2 * Real.log (Real.log x) + 3 := by
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  -- `y := Nat.log 2 x ≥ 4`
  set y := Nat.log 2 x with hy
  have hy4 : 4 ≤ y := by
    rw [hy]
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  -- `nBlocks (zC x) ≤ Nat.log 2 y + 1`
  have hmono : nBlocks (zC x) ≤ Nat.log 2 y + 1 := by
    unfold nBlocks
    have := Nat.log_mono_right (b := 2) (Nat.log_mono_right (b := 2) (zC_le_self (by omega : 1 ≤ x)))
    rw [← hy] at this
    omega
  have hmono' : (nBlocks (zC x) : ℝ) ≤ (Nat.log 2 y : ℝ) + 1 := by exact_mod_cast hmono
  -- `Nat.log 2 y ≤ log y / log 2 ≤ (log log x + log 2) / log 2`
  have h1 := natLog_le_log_div (by omega : 1 ≤ y)
  have hy_le : (y : ℝ) ≤ Real.log x / Real.log 2 := natLog_le_log_div (by omega : 1 ≤ x)
  have h2 : Real.log y ≤ Real.log (Real.log x / Real.log 2) :=
    Real.log_le_log (by positivity) hy_le
  rw [Real.log_div hLpos.ne' (by positivity)] at h2
  have h3 : Real.log (Real.log 2) ≥ -1 := by
    have : Real.log (1 / 2 : ℝ) ≤ Real.log (Real.log 2) := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at this
    linarith
  have hℓ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by
    have : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith)
  have h4 : (Nat.log 2 y : ℝ) ≤ 2 * Real.log (Real.log x) + 2 := by
    calc (Nat.log 2 y : ℝ) ≤ Real.log y / Real.log 2 := h1
      _ ≤ (Real.log (Real.log x) + 1) / Real.log 2 := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          linarith
      _ ≤ (Real.log (Real.log x) + 1) / (1 / 2) := by
          apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
      _ = 2 * Real.log (Real.log x) + 2 := by ring
  linarith

/-! ### Main and remainder terms -/

theorem log_le_2000_rpow {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2000 * x ^ (1 / 2000 : ℝ) := by
  calc Real.log x ≤ x ^ (1 / 2000 : ℝ) / (1 / 2000) := Real.log_le_rpow_div hx (by norm_num)
    _ = 2000 * x ^ (1 / 2000 : ℝ) := by ring

/-- `(log x)^n ≤ 2000^n x^{n/2000}`. -/
theorem log_pow_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (Real.log x) ^ n ≤ 2000 ^ n * x ^ ((n : ℝ) / 2000) := by
  have hx0 : 0 ≤ x := by linarith
  calc (Real.log x) ^ n ≤ (2000 * x ^ (1 / 2000 : ℝ)) ^ n :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (log_le_2000_rpow hx0) n
    _ = 2000 ^ n * (x ^ (1 / 2000 : ℝ)) ^ (n : ℕ) := by rw [mul_pow]
    _ = 2000 ^ n * x ^ ((n : ℝ) / 2000) := by
        rw [← Real.rpow_natCast (x ^ (1 / 2000 : ℝ)) n, ← Real.rpow_mul hx0]
        congr 1
        ring_nf

theorem exp_nat_mul_loglog {x : ℝ} (hx : 0 < Real.log x) (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log (Real.log x)) = (Real.log x) ^ n := by
  rw [← Real.log_pow, Real.exp_log (pow_pos hx n)]

theorem exp_neg_nat_mul_loglog {x : ℝ} (hx : 0 < Real.log x) (n : ℕ) :
    Real.exp (-((n : ℝ) * Real.log (Real.log x))) = ((Real.log x) ^ n)⁻¹ := by
  rw [Real.exp_neg, exp_nat_mul_loglog hx n]

/-- For large `x`, the sifted count at level `zC x` is at least `x^{4/5}`. -/
theorem brunBounded_count_ge : ∀ᶠ x : ℕ in atTop,
    (x : ℝ) ^ (4 / 5 : ℝ) ≤
      (#{n ∈ range (x + 1) | Nat.Coprime (primorial (zC x)) (n * (n + 2))} : ℝ) := by
  filter_upwards [eventually_ge_atTop 16, eventually_loglog_ge 4,
    eventually_rpow_ge (Real.exp 12 * 2000 ^ 9) (by norm_num : (0 : ℝ) < 19 / 2000),
    eventually_rpow_ge (2 * Real.exp 288 * 2000 ^ 192) (by norm_num : (0 : ℝ) < 1 / 250),
    eventually_rpow_ge 2 (by norm_num : (0 : ℝ) < 1 / 2000)] with x hx16 hℓ hA hB hD
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1' : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log x := Real.log_pos hx1'
  have hz1 : 1 ≤ zC x := by
    unfold zC
    apply Nat.le_floor
    push_cast
    linarith
  have hcount := brunHooley_twin_count_ge x (zC x) hz1
  have hr_le : (nBlocks (zC x) : ℝ) ≤ 2 * Real.log (Real.log x) + 3 := nBlocks_zC_le hx16
  have hr0 : (0 : ℝ) ≤ nBlocks (zC x) := by positivity
  -- remainder: `(r+1) e^{4r} z^{972} ≤ x^{1/2}`
  have hrem : ((nBlocks (zC x) : ℝ) + 1) *
      (Real.exp (4 * nBlocks (zC x)) * (zC x : ℝ) ^ (972 : ℝ)) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
    have hz972 : (zC x : ℝ) ^ (972 : ℝ) ≤ (x : ℝ) ^ (972 / 2000 : ℝ) := by
      calc (zC x : ℝ) ^ (972 : ℝ) ≤ ((x : ℝ) ^ (1 / 2000 : ℝ)) ^ (972 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (zC_le_rpow x) (by norm_num)
        _ = (x : ℝ) ^ (972 / 2000 : ℝ) := by
            rw [← Real.rpow_mul hxpos.le]; norm_num
    have hexp : Real.exp (4 * nBlocks (zC x)) ≤ Real.exp 12 * (Real.log x) ^ 8 := by
      calc Real.exp (4 * nBlocks (zC x)) ≤ Real.exp (4 * (2 * Real.log (Real.log x) + 3)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp 12 * Real.exp ((8 : ℕ) * Real.log (Real.log x)) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring
        _ = Real.exp 12 * (Real.log x) ^ 8 := by rw [exp_nat_mul_loglog hLpos]
    have hr1 : (nBlocks (zC x) : ℝ) + 1 ≤ Real.log x := by
      have h1 : 2 * Real.log (Real.log x) + 4 ≤ Real.exp (Real.log (Real.log x)) := by
        have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))
        nlinarith
      rw [Real.exp_log hLpos] at h1
      linarith
    have hL9 : (Real.log x) ^ 9 ≤ 2000 ^ 9 * (x : ℝ) ^ ((9 : ℝ) / 2000) := by
      have := log_pow_le hx1 9
      push_cast at this
      exact this
    calc ((nBlocks (zC x) : ℝ) + 1) * (Real.exp (4 * nBlocks (zC x)) * (zC x : ℝ) ^ (972 : ℝ))
        ≤ Real.log x * (Real.exp 12 * (Real.log x) ^ 8 * (x : ℝ) ^ (972 / 2000 : ℝ)) := by
          apply mul_le_mul hr1 _ (by positivity) hLpos.le
          exact mul_le_mul hexp hz972 (by positivity) (by positivity)
      _ = Real.exp 12 * (Real.log x) ^ 9 * (x : ℝ) ^ (972 / 2000 : ℝ) := by ring
      _ ≤ Real.exp 12 * (2000 ^ 9 * (x : ℝ) ^ ((9 : ℝ) / 2000)) * (x : ℝ) ^ (972 / 2000 : ℝ) := by
          gcongr
      _ = (Real.exp 12 * 2000 ^ 9) * (x : ℝ) ^ ((9 : ℝ) / 2000 + 972 / 2000) := by
          rw [Real.rpow_add hxpos]; ring
      _ ≤ (x : ℝ) ^ (19 / 2000 : ℝ) * (x : ℝ) ^ ((9 : ℝ) / 2000 + 972 / 2000) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = (x : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
  -- main: `(x+1) e^{-96 r}/2 ≥ x^{9/10}`
  have hmain : (x : ℝ) ^ (9 / 10 : ℝ) ≤
      ((x : ℝ) + 1) * Real.exp (-(96 * (nBlocks (zC x) : ℝ))) / 2 := by
    have hexp : Real.exp (-288) * ((Real.log x) ^ 192)⁻¹ ≤
        Real.exp (-(96 * (nBlocks (zC x) : ℝ))) := by
      calc Real.exp (-288) * ((Real.log x) ^ 192)⁻¹
          = Real.exp (-288) * Real.exp (-((192 : ℕ) * Real.log (Real.log x))) := by
            rw [exp_neg_nat_mul_loglog hLpos]
        _ = Real.exp (-(96 * (2 * Real.log (Real.log x) + 3))) := by
            rw [← Real.exp_add]; congr 1; push_cast; ring
        _ ≤ Real.exp (-(96 * (nBlocks (zC x) : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hL192 : (Real.log x) ^ 192 ≤ 2000 ^ 192 * (x : ℝ) ^ ((192 : ℝ) / 2000) := by
      have := log_pow_le hx1 192
      push_cast at this
      exact this
    have hL192pos : 0 < (Real.log x) ^ 192 := by positivity
    have hkey : 2 * Real.exp 288 * (Real.log x) ^ 192 ≤ (x : ℝ) ^ (1 / 10 : ℝ) := by
      calc 2 * Real.exp 288 * (Real.log x) ^ 192
          ≤ 2 * Real.exp 288 * (2000 ^ 192 * (x : ℝ) ^ ((192 : ℝ) / 2000)) := by gcongr
        _ = (2 * Real.exp 288 * 2000 ^ 192) * (x : ℝ) ^ ((192 : ℝ) / 2000) := by ring
        _ ≤ (x : ℝ) ^ (1 / 250 : ℝ) * (x : ℝ) ^ ((192 : ℝ) / 2000) :=
            mul_le_mul_of_nonneg_right hB (by positivity)
        _ = (x : ℝ) ^ (1 / 10 : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
    have hx910 : (x : ℝ) ^ (9 / 10 : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) = x := by
      rw [← Real.rpow_add hxpos]; norm_num
    have hexp288 : 0 < Real.exp 288 := Real.exp_pos _
    have hx910pos : 0 < (x : ℝ) ^ (9 / 10 : ℝ) := by positivity
    have h1 : (x : ℝ) ^ (9 / 10 : ℝ) * (2 * Real.exp 288 * (Real.log x) ^ 192) ≤ x := by
      calc (x : ℝ) ^ (9 / 10 : ℝ) * (2 * Real.exp 288 * (Real.log x) ^ 192)
          ≤ (x : ℝ) ^ (9 / 10 : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_left hkey hx910pos.le
        _ = x := hx910
    have h2 : (x : ℝ) ^ (9 / 10 : ℝ) ≤ x * (Real.exp (-288) * ((Real.log x) ^ 192)⁻¹) / 2 := by
      have hpos : 0 < Real.exp 288 * (Real.log x) ^ 192 := by positivity
      rw [Real.exp_neg, ← mul_inv, le_div_iff₀ (by norm_num), le_mul_inv_iff₀ hpos]
      linarith
    calc (x : ℝ) ^ (9 / 10 : ℝ) ≤ x * (Real.exp (-288) * ((Real.log x) ^ 192)⁻¹) / 2 := h2
      _ ≤ ((x : ℝ) + 1) * Real.exp (-(96 * (nBlocks (zC x) : ℝ))) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          apply mul_le_mul (by linarith) hexp (by positivity) (by positivity)
  -- combine
  have hsub : (x : ℝ) ^ (4 / 5 : ℝ) ≤ (x : ℝ) ^ (9 / 10 : ℝ) - (x : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : (x : ℝ) ^ (9 / 10 : ℝ) = (x : ℝ) ^ (4 / 5 : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    have h2 : (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h3 : (0 : ℝ) ≤ (x : ℝ) ^ (4 / 5 : ℝ) := by positivity
    have h4 : (2 : ℝ) ≤ (x : ℝ) ^ (1 / 10 : ℝ) := by
      calc (2 : ℝ) ≤ (2 : ℝ) ^ (200 : ℝ) := by
            calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
              _ ≤ (2 : ℝ) ^ (200 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ ((x : ℝ) ^ (1 / 2000 : ℝ)) ^ (200 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) hD (by norm_num)
        _ = (x : ℝ) ^ (1 / 10 : ℝ) := by rw [← Real.rpow_mul hxpos.le]; norm_num
    nlinarith
  linarith

/-- **Brun's theorem (bounded form).** There are infinitely many `n` such that `n` and `n + 2`
together have at most `4001` prime factors (with multiplicity). -/
theorem brun_bounded_infinite :
    {n : ℕ | Ω n + Ω (n + 2) ≤ 4001}.Infinite := by
  set S := {n : ℕ | Ω n + Ω (n + 2) ≤ 4001} with hS
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hev : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (4 / 5 : ℝ) ≤ hfin.toFinset.card := by
    filter_upwards [brunBounded_count_ge, eventually_ge_atTop 16, eventually_log_ge 4000,
      eventually_rpow_ge 2 (by norm_num : (0 : ℝ) < 1 / 2000)] with x hcount hx16 hL hD
    have hx1' : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    have hxpos : (0 : ℝ) < x := by linarith
    have hLpos : 0 < Real.log x := by linarith
    -- every sifted `n` lies in `S`
    have hsub : {n ∈ range (x + 1) | Nat.Coprime (primorial (zC x)) (n * (n + 2))} ⊆
        hfin.toFinset := by
      intro n hn
      rw [mem_filter, mem_range] at hn
      rw [Set.Finite.mem_toFinset, hS, Set.mem_setOf_eq]
      have hz2 : 2 ≤ zC x := by
        unfold zC; apply Nat.le_floor; push_cast; exact hD
      have hn0 : n ≠ 0 := by
        rintro rfl
        have := (coprime_primorial_iff.mp hn.2) 2 Nat.prime_two (by omega) (by simp)
        exact this
      have hN0 : n * (n + 2) ≠ 0 := by positivity
      have hrough : ∀ p, p.Prime → p ∣ n * (n + 2) → zC x < p := by
        intro p hp hpn
        by_contra h
        exact (coprime_primorial_iff.mp hn.2) p hp (by omega) hpn
      have hpow := pow_cardFactors_le hN0 hrough
      have hpow' : ((zC x : ℝ) + 1) ^ (Ω (n * (n + 2))) ≤ ((x : ℝ) + 2) ^ 2 := by
        calc ((zC x : ℝ) + 1) ^ (Ω (n * (n + 2))) =
              (((zC x + 1) ^ (Ω (n * (n + 2))) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((n * (n + 2) : ℕ) : ℝ) := by exact_mod_cast hpow
          _ ≤ ((x : ℝ) + 2) ^ 2 := by
              push_cast
              have : (n : ℝ) ≤ x := by exact_mod_cast (by omega : n ≤ x)
              nlinarith
      have hlog := Real.log_le_log (by positivity) hpow'
      rw [Real.log_pow, Real.log_pow] at hlog
      push_cast at hlog
      -- `log (z+1) ≥ log x / 2000`
      have hlogz : Real.log x / 2000 ≤ Real.log ((zC x : ℝ) + 1) := by
        have h1 : Real.log ((x : ℝ) ^ (1 / 2000 : ℝ)) ≤ Real.log ((zC x : ℝ) + 1) :=
          Real.log_le_log (by positivity) (rpow_lt_zC_add_one x).le
        rw [Real.log_rpow hxpos] at h1
        linarith
      -- `log (x + 2) ≤ log x + 1`
      have hlogx2 : Real.log ((x : ℝ) + 2) ≤ Real.log x + 1 := by
        have : (x : ℝ) + 2 ≤ Real.exp 1 * x := by
          have := Real.exp_one_gt_d9
          have hx16r : (16 : ℝ) ≤ x := by exact_mod_cast hx16
          nlinarith
        calc Real.log ((x : ℝ) + 2) ≤ Real.log (Real.exp 1 * x) :=
              Real.log_le_log (by positivity) this
          _ = Real.log x + 1 := by
              rw [Real.log_mul (Real.exp_pos _).ne' hxpos.ne', Real.log_exp]; ring
      have hΩ : ((Ω (n * (n + 2)) : ℕ) : ℝ) ≤ 4001 := by
        have hlz : 0 < Real.log ((zC x : ℝ) + 1) := by linarith
        have h1 : ((Ω (n * (n + 2)) : ℕ) : ℝ) * (Real.log x / 2000) ≤ 2 * (Real.log x + 1) := by
          calc ((Ω (n * (n + 2)) : ℕ) : ℝ) * (Real.log x / 2000)
              ≤ ((Ω (n * (n + 2)) : ℕ) : ℝ) * Real.log ((zC x : ℝ) + 1) :=
                mul_le_mul_of_nonneg_left hlogz (by positivity)
            _ ≤ 2 * Real.log ((x : ℝ) + 2) := hlog
            _ ≤ 2 * (Real.log x + 1) := by linarith
        -- so `Ω ≤ 4000 (1 + 1/log x) ≤ 4001`
        have : ((Ω (n * (n + 2)) : ℕ) : ℝ) * Real.log x ≤ 4000 * Real.log x + 4000 := by
          linarith
        nlinarith
      rw [← ArithmeticFunction.cardFactors_mul hn0 (by omega)]
      exact_mod_cast hΩ
    calc (x : ℝ) ^ (4 / 5 : ℝ)
        ≤ (#{n ∈ range (x + 1) | Nat.Coprime (primorial (zC x)) (n * (n + 2))} : ℝ) := hcount
      _ ≤ hfin.toFinset.card := by exact_mod_cast card_le_card hsub
  have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (4 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨x, hx1, hx2⟩ := ((tendsto_atTop.mp hlim (hfin.toFinset.card + 1)).and hev).exists
  have hx1' : (hfin.toFinset.card : ℝ) + 1 ≤ (x : ℝ) ^ (4 / 5 : ℝ) := hx1
  linarith

end TwinPrime
