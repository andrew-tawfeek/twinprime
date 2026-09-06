import TwinPrime.Analytic.WideLocalLogDerivativeExpansion
import TwinPrime.Analytic.ZetaLocalExpansion

/-!
# Regularized zeta zero expansions on radius 17/16

The expansion uses the actual zeros of the entire regularization `Z` on
radius `5/4`. Its remainder has constant `288` on radius `17/16`. A
companion statement keeps the pole exactly when returning to zeta itself.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

/-- Jensen counts the actual zeros of the entire regularization on the
closed radius-5/4 disk, with multiplicity and no pole contribution. -/
theorem sum_divisor_regularizedZeta_le_log_height (c : ℂ) (hc : c.re = 2) :
    (((∑ᶠ u, divisor regularizedRiemannZeta (closedBall c (5 / 4)) u) : ℤ) : ℝ) ≤
      (Real.log 16 + 2 * Real.log (‖c‖ + 2)) / Real.log (6 / 5) := by
  let M : ℝ := 4 * (‖c‖ + 2) ^ 2
  have hn := norm_nonneg c
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg ‖c‖]
  have hcenter := one_quarter_le_norm_regularizedRiemannZeta_center c hc
  have hcenter0 : 0 < ‖regularizedRiemannZeta c‖ := by linarith
  have hf : AnalyticOnNhd ℂ regularizedRiemannZeta (closedBall c |(3 / 2 : ℝ)|) :=
    fun w _ => differentiable_regularizedRiemannZeta.analyticAt w
  have hbound : ∀ w ∈ sphere c |(3 / 2 : ℝ)|, ‖regularizedRiemannZeta w‖ ≤ M := by
    intro w hw
    have ht := norm_regularizedRiemannZeta_le_on_closedBall c (3 / 2)
      (by rw [hc]; norm_num) w (sphere_subset_closedBall
        (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using hw))
    have ht' : ‖regularizedRiemannZeta w‖ ≤
        regularizedZetaGrowthBudget (1 / 2) (‖c‖ + 3 / 2) := by
      simpa only [hc, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using ht
    exact ht'.trans (regularizedZetaGrowthBudget_half_le c)
  have hj := hf.sum_divisor_le (r := (5 / 4 : ℝ)) (R := (3 / 2 : ℝ))
    (by norm_num) (by norm_num) hM (norm_pos_iff.mp hcenter0) hbound
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at hj
  norm_num at hj
  apply hj.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have hratio : M / ‖regularizedRiemannZeta c‖ ≤ 16 * (‖c‖ + 2) ^ 2 := by
    calc
      _ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hcenter
      _ = _ := by dsimp [M]; ring
  have hH : 0 < ‖c‖ + 2 := by positivity
  calc
    _ ≤ Real.log (16 * (‖c‖ + 2) ^ 2) :=
      Real.log_le_log (div_pos (by linarith) hcenter0) hratio
    _ = _ := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hH.ne'), Real.log_pow]
      norm_num

theorem wide_norm_logDeriv_regularizedZeta_sub_zero_sum_le
    (c : ℂ) (hc : c.re = 2) (z : ℂ) (hz : z ∈ closedBall c (17 / 16))
    (hZz : regularizedRiemannZeta z ≠ 0) :
    ‖logDeriv regularizedRiemannZeta z - localZetaZeroSum c z‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (‖c‖ + 2)) := by
  let M : ℝ := 4 * (‖c‖ + 2) ^ 2
  have hn := norm_nonneg c
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg ‖c‖]
  have hcenter := one_quarter_le_norm_regularizedRiemannZeta_center c hc
  have hcenter0 : 0 < ‖regularizedRiemannZeta c‖ := by linarith
  have hf : AnalyticOnNhd ℂ regularizedRiemannZeta (closedBall c (3 / 2)) :=
    fun w _ => differentiable_regularizedRiemannZeta.analyticAt w
  have hbound : ∀ w ∈ sphere c (3 / 2), ‖regularizedRiemannZeta w‖ ≤ M := by
    intro w hw
    have ht := norm_regularizedRiemannZeta_le_on_closedBall c (3 / 2)
      (by rw [hc]; norm_num) w (sphere_subset_closedBall hw)
    have ht' : ‖regularizedRiemannZeta w‖ ≤
        regularizedZetaGrowthBudget (1 / 2) (‖c‖ + 3 / 2) := by
      simpa only [hc, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using ht
    exact ht'.trans (regularizedZetaGrowthBudget_half_le c)
  have he := wide_norm_logDeriv_sub_zero_sum_le hf (norm_pos_iff.mp hcenter0) hM hbound z hz hZz
  apply he.trans
  have hratio : M / ‖regularizedRiemannZeta c‖ ≤ 16 * (‖c‖ + 2) ^ 2 := by
    calc
      _ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hcenter
      _ = _ := by dsimp [M]; ring
  have hH : 0 < ‖c‖ + 2 := by positivity
  have hlog : Real.log (M / ‖regularizedRiemannZeta c‖) ≤
      Real.log 16 + 2 * Real.log (‖c‖ + 2) := by
    calc
      _ ≤ Real.log (16 * (‖c‖ + 2) ^ 2) :=
        Real.log_le_log (div_pos (by linarith) hcenter0) hratio
      _ = _ := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hH.ne'), Real.log_pow]
        norm_num
  apply mul_le_mul_of_nonneg_left (by linarith)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  positivity

/-- This includes z=1 through the entire regularization, whose value there is one. -/
theorem wide_norm_logDeriv_regularizedZeta_sub_zero_sum_le_of_one_le_re
    (c : ℂ) (hc : c.re = 2) (z : ℂ) (hz : z ∈ closedBall c (17 / 16))
    (hre : 1 ≤ z.re) :
    ‖logDeriv regularizedRiemannZeta z - localZetaZeroSum c z‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (‖c‖ + 2)) :=
  wide_norm_logDeriv_regularizedZeta_sub_zero_sum_le c hc z hz
    (regularizedRiemannZeta_ne_zero_of_one_le_re z hre)

/-- The pole is retained exactly for the unregularized logarithmic derivative. -/
theorem wide_norm_logDeriv_zeta_add_pole_sub_zero_sum_le
    (c : ℂ) (hc : c.re = 2) (z : ℂ) (hz : z ∈ closedBall c (17 / 16))
    (hz1 : z ≠ 1) (hZz : regularizedRiemannZeta z ≠ 0) :
    ‖logDeriv riemannZeta z + 1 / (z - 1) - localZetaZeroSum c z‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (‖c‖ + 2)) := by
  have he := neg_zeta_logDerivative_eq_pole_sub_regularized z hz1 hZz
  rw [neg_div] at he
  have he' : logDeriv riemannZeta z + 1 / (z - 1) =
      logDeriv regularizedRiemannZeta z := by
    simp only [logDeriv_apply]
    linear_combination -he
  rw [he']
  exact wide_norm_logDeriv_regularizedZeta_sub_zero_sum_le c hc z hz hZz

end TwinPrime.Analytic
