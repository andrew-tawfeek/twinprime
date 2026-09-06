import TwinPrime.Analytic.ClassicalCorrelationCenter
import TwinPrime.Analytic.LogPowerDistribution
import TwinPrime.Analytic.LogPowerEvenBudget
import TwinPrime.Analytic.MixedTypeICorrelation

/-!
# Logarithmic precision for the exact finite classical center

All fixed logarithmic weights are allowed. The numerical product bound has
a fixed exponent strictly below one half; no signed lower bound is assumed.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

theorem MaximalBombieriVinogradov.tendsto_classicalCenter_error_div_mul_log_pow
    (hBV : MaximalBombieriVinogradov) (U V : ℕ → ℕ) (a : ℝ)
    (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hU : ∀ᶠ X : ℕ in atTop, 1 ≤ U X) (hV : ∀ᶠ X : ℕ in atTop, 1 ≤ V X)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a)
    (k : ℕ) :
    Tendsto (fun X : ℕ =>
      |W2 X - (bilinearTerm (U X) (V X) X + classicalCorrelationCenter (U X) (V X) X)| /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  have h := ((hBV.tendsto_log_pow_mul_sum_error_div_of_power_level
      (fun X => U X * V X) a haHalf hUV (k + 1)).const_mul 8).add
    ((tendsto_mixedEvenWeightBudget_div_mul_log_pow U V a ha haHalf hUV k).const_mul 3)
  simp only [mul_zero, zero_add] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg X))
      (pow_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)) k)
  · filter_upwards [hUV, hU, hV, eventually_ge_atTop 1] with X hprod hUX hVX hX
    have hprodX : U X * V X ≤ X := by
      exact_mod_cast hprod.trans (Real.rpow_le_self_of_one_le
        (by exact_mod_cast hX) (by linarith : a ≤ 1))
    have hlog : 0 ≤ Real.log (2 * (X : ℝ) + 2) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
    have hb := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (classicalCorrelationCenter_error_le_product (U X) (V X) X hUX hVX hprodX)
        (Nat.cast_nonneg (α := ℝ) X)) (pow_nonneg hlog k)
    convert hb using 1
    simp only [mixedEvenWeightBudget, Nat.cast_mul, pow_succ]
    ring

theorem MaximalBombieriVinogradov.tendsto_mixed_typeI_error_div_mul_log_pow
    (hBV : MaximalBombieriVinogradov) (U V : ℕ → ℕ) (a : ℝ)
    (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a)
    (k : ℕ) :
    Tendsto (fun X : ℕ =>
      (typeITerm (U X) (V X) X - (X : ℝ) * totientTypeIMain (U X) (V X)) /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  have h := ((hBV.tendsto_log_pow_mul_sum_error_div_of_power_level
      (fun X => U X * V X) a haHalf hUV (k + 1)).const_mul 2).add
    (tendsto_mixedEvenWeightBudget_div_mul_log_pow U V a ha haHalf hUV k)
  simp only [mul_zero, zero_add] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hUV, eventually_ge_atTop 1] with X hprod hX
    have hprodX : U X * V X ≤ X := by
      exact_mod_cast hprod.trans (Real.rpow_le_self_of_one_le
        (by exact_mod_cast hX) (by linarith : a ≤ 1))
    have hlog : 0 ≤ Real.log (2 * (X : ℝ) + 2) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
    dsimp only [Function.comp_def]
    rw [abs_mul, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X),
      abs_of_nonneg (pow_nonneg hlog k)]
    have hb := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (typeICorrelation_error_le_mixed (U X) (V X) X hprodX)
        (Nat.cast_nonneg (α := ℝ) X)) (pow_nonneg hlog k)
    convert hb using 1
    simp only [pow_succ]
    ring

theorem MaximalBombieriVinogradov.tendsto_centered_bilinear_cutoff_shift_div_mul_log_pow
    (hBV : MaximalBombieriVinogradov) (U V W : ℕ → ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (haHalf : a < 1 / 2) (hb : 0 ≤ b) (hbHalf : b < 1 / 2)
    (hV : ∀ᶠ X : ℕ in atTop, V X ≤ X) (hW : ∀ᶠ X : ℕ in atTop, W X ≤ X)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a)
    (hUW : ∀ᶠ X : ℕ in atTop, ((U X * W X : ℕ) : ℝ) ≤ (X : ℝ) ^ b)
    (k : ℕ) :
    Tendsto (fun X : ℕ =>
      ((bilinearTerm (U X) (V X) X + classicalCorrelationCenter (U X) (V X) X) -
        (bilinearTerm (U X) (W X) X + classicalCorrelationCenter (U X) (W X) X)) /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  have h := (hBV.tendsto_mixed_typeI_error_div_mul_log_pow U V a ha haHalf hUV k).sub
    (hBV.tendsto_mixed_typeI_error_div_mul_log_pow U W b hb hbHalf hUW k)
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [hV, hW] with X hVX hWX
  rw [centered_bilinear_cutoff_shift_eq (U X) (V X) (W X) X hVX hWX]
  ring

end TwinPrime.Analytic
