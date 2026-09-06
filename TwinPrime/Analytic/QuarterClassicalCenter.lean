import TwinPrime.Analytic.ClassicalCenterPrecision
import TwinPrime.Analytic.QuarterBilinearReduction

/-!
# The finite classical center at the primary and quarter cutoffs

The actual Bombieri--Vinogradov theorem gives every fixed logarithmic saving
for the errors around the finite classical center. The primary-to-quarter
change is centered with the respective finite Type I main terms. Replacing
the quarter beta coefficient by its prime-only part preserves this precision.
None of these estimates is a signed lower bound for the centered expression.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

private theorem primary_product_power_bound :
    ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * primaryCutoff X : ℕ) : ℝ) ≤ (X : ℝ) ^ (2 / 5 : ℝ) := by
  filter_upwards with X
  simpa only [pow_two] using primaryCutoff_sq_le_rpow X

private theorem quarter_product_power_bound :
    ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * quarterCutoff X : ℕ) : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with X hX
  simpa only [Nat.cast_mul] using primaryCutoff_mul_quarterCutoff_le_rpow X hX

/-- The exact primary classical center has all fixed logarithmic precision. -/
theorem tendsto_primary_classicalCenter_error_div_mul_log_pow (k : ℕ) :
    Tendsto (fun X : ℕ =>
      |W2 X - (bilinearTerm (primaryCutoff X) (primaryCutoff X) X +
        classicalCorrelationCenter (primaryCutoff X) (primaryCutoff X) X)| /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  apply maximal_bombieri_vinogradov.tendsto_classicalCenter_error_div_mul_log_pow
    primaryCutoff primaryCutoff (2 / 5) (by norm_num) (by norm_num)
    _ _ primary_product_power_bound k
  all_goals
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact primaryCutoff_pos hX

/-- The mixed fifth-root/fourth-root classical center has the same precision. -/
theorem tendsto_quarter_classicalCenter_error_div_mul_log_pow (k : ℕ) :
    Tendsto (fun X : ℕ =>
      |W2 X - (bilinearTerm (primaryCutoff X) (quarterCutoff X) X +
        classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X)| /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  apply maximal_bombieri_vinogradov.tendsto_classicalCenter_error_div_mul_log_pow
    primaryCutoff quarterCutoff (9 / 20) (by norm_num) (by norm_num)
    _ _ quarter_product_power_bound k
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact primaryCutoff_pos hX
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact quarterCutoff_pos hX

/-- The centered cutoff change loses no fixed power of the logarithm. -/
theorem tendsto_primary_centered_bilinear_sub_quarter_div_mul_log_pow (k : ℕ) :
    Tendsto (fun X : ℕ =>
      ((bilinearTerm (primaryCutoff X) (primaryCutoff X) X +
          classicalCorrelationCenter (primaryCutoff X) (primaryCutoff X) X) -
        (bilinearTerm (primaryCutoff X) (quarterCutoff X) X +
          classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X)) /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  apply maximal_bombieri_vinogradov.tendsto_centered_bilinear_cutoff_shift_div_mul_log_pow
    primaryCutoff primaryCutoff quarterCutoff (2 / 5) (9 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ _ primary_product_power_bound quarter_product_power_bound k
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact primaryCutoff_le hX
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact quarterCutoff_le hX

/-- The prime-only replacement error also permits the smaller logarithm used
by the classical center, uniformly in the choice of left cutoff. -/
theorem tendsto_quarter_abs_bilinear_sub_primeBeta_div_mul_log_two_pow
    (U : ℕ → ℕ) (k : ℕ) :
    Tendsto (fun X : ℕ =>
      |bilinearTerm (U X) (quarterCutoff X) X -
        bilinearPrimeBeta (U X) (quarterCutoff X) X| /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  have h := (tendsto_quarter_bilinear_sub_primeBeta_div_mul_log_pow U k).abs
  simp only [abs_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg X))
      (pow_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) X
        linarith)) k)
  · filter_upwards with X
    have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hL2 : 0 ≤ Real.log (2 * (X : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hL4 : 0 ≤ Real.log (4 * (X : ℝ) + 4) := Real.log_nonneg (by linarith)
    have hlog : Real.log (2 * (X : ℝ) + 2) ≤ Real.log (4 * (X : ℝ) + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [abs_mul, abs_div, abs_of_nonneg hX, abs_of_nonneg (pow_nonneg hL4 k)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL2 hlog k)
      (div_nonneg (abs_nonneg _) hX)

/-- The actual quarter prime-beta sum plus the finite classical center
approximates W2 after every fixed logarithmic weight. -/
theorem tendsto_quarter_primeBeta_classicalCenter_error_div_mul_log_pow (k : ℕ) :
    Tendsto (fun X : ℕ =>
      |W2 X - (bilinearPrimeBeta (primaryCutoff X) (quarterCutoff X) X +
        classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X)| /
        X * Real.log (2 * X + 2) ^ k) atTop (nhds 0) := by
  have h := (tendsto_quarter_classicalCenter_error_div_mul_log_pow k).add
    (tendsto_quarter_abs_bilinear_sub_primeBeta_div_mul_log_two_pow primaryCutoff k)
  simp only [zero_add] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg X))
      (pow_nonneg (Real.log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) X
        linarith)) k)
  · filter_upwards with X
    have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hlog : 0 ≤ Real.log (2 * (X : ℝ) + 2) := Real.log_nonneg (by linarith)
    have htri :
        |W2 X - (bilinearPrimeBeta (primaryCutoff X) (quarterCutoff X) X +
          classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X)| ≤
        |W2 X - (bilinearTerm (primaryCutoff X) (quarterCutoff X) X +
          classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X)| +
        |bilinearTerm (primaryCutoff X) (quarterCutoff X) X -
          bilinearPrimeBeta (primaryCutoff X) (quarterCutoff X) X| := by
      have heq :
          W2 X - (bilinearPrimeBeta (primaryCutoff X) (quarterCutoff X) X +
            classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X) =
          (W2 X - (bilinearTerm (primaryCutoff X) (quarterCutoff X) X +
            classicalCorrelationCenter (primaryCutoff X) (quarterCutoff X) X)) +
          (bilinearTerm (primaryCutoff X) (quarterCutoff X) X -
            bilinearPrimeBeta (primaryCutoff X) (quarterCutoff X) X) := by ring
      rw [heq]
      exact abs_add_le _ _
    simpa only [add_div, add_mul] using
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htri hX) (pow_nonneg hlog k)

end TwinPrime.Analytic
