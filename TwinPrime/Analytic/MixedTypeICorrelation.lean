import TwinPrime.Analytic.PowerLevelDistribution
import TwinPrime.Analytic.MixedEvenBudget
import TwinPrime.Analytic.TypeICorrelation

/-!
# The Type I error for mixed cutoffs below the square-root level

The same exact main coefficient, including shared prime factors, is retained.
Both odd progression errors and even-modulus exceptions are summed over the
complete product of the two independently chosen cutoffs.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

theorem typeICorrelation_error_le_mixed (U V X : ℕ) (hUV : U * V ≤ X) :
    |typeITerm U V X - (X : ℝ) * totientTypeIMain U V| ≤
      2 * Real.log (2 * X + 2) *
        (∑ q ∈ Icc 1 (U * V), progressionMaxError (2 * X + 2) q) +
      mixedEvenWeightBudget U V X := by
  have hL : 0 ≤ Real.log (U * V + 1) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) (U * V)
    push_cast at this
    linarith
  have hLog : Real.log (U * V + 1) ≤ Real.log (2 * X + 2) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show U * V + 1 ≤ 2 * X + 2 by omega)
  apply (typeICorrelation_error_le U V X).trans
  apply _root_.add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLog (by norm_num))
      (sum_nonneg fun q _ => progressionMaxError_nonneg _ q)
  · unfold mixedEvenWeightBudget
    push_cast
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLog (by positivity)) (evenProgressionBound_nonneg X)

theorem MaximalBombieriVinogradov.tendsto_mixed_typeI_error_div
    (hBV : MaximalBombieriVinogradov) (U V : ℕ → ℕ) (a : ℝ)
    (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    Tendsto (fun X : ℕ =>
      (typeITerm (U X) (V X) X - (X : ℝ) * totientTypeIMain (U X) (V X)) / X)
      atTop (nhds 0) := by
  have h := ((hBV.tendsto_log_mul_sum_error_div_of_power_level
      (fun X => U X * V X) a haHalf hUV).const_mul 2).add
    (tendsto_mixedEvenWeightBudget_div_of_product_le U V a ha haHalf hUV)
  simp only [mul_zero, zero_add] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [hUV, eventually_ge_atTop 1] with X hprod hX
    have hprodX : U X * V X ≤ X := by
      have hp := hprod.trans (Real.rpow_le_self_of_one_le (by exact_mod_cast hX)
        (by linarith : a ≤ 1))
      exact_mod_cast hp
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)]
    have hb := div_le_div_of_nonneg_right (typeICorrelation_error_le_mixed (U X) (V X) X hprodX)
      (Nat.cast_nonneg (α := ℝ) X)
    simpa only [add_div, mul_div_assoc, mul_assoc] using hb

theorem MaximalBombieriVinogradov.tendsto_mixed_typeI_div_sub_main
    (hBV : MaximalBombieriVinogradov) (U V : ℕ → ℕ) (a : ℝ)
    (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    Tendsto (fun X : ℕ => typeITerm (U X) (V X) X / X - totientTypeIMain (U X) (V X))
      atTop (nhds 0) := by
  apply (hBV.tendsto_mixed_typeI_error_div U V a ha haHalf hUV).congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  field_simp

end TwinPrime.Analytic
