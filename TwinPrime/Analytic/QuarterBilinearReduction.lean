import TwinPrime.Analytic.MixedTypeICorrelation
import TwinPrime.Analytic.BilinearCutoffShift
import TwinPrime.Analytic.QuarterCutoff
import TwinPrime.Analytic.ClassicalDistribution
import TwinPrime.Analytic.PrimeBetaReduction

/-!
# Removing the beta band up to a fourth-root cutoff

The left cutoff remains the fifth root. The right cutoff can be raised to
the fourth root at signed o(X) cost, using the independently proved classical
inputs. This is a whole-sum estimate, not a factorwise absolute band bound.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

theorem tendsto_totientTypeIMain_primary_of_right_le (W : ℕ → ℕ)
    (hW : ∀ᶠ X : ℕ in atTop, W X ≤ X) :
    Tendsto (fun X : ℕ => totientTypeIMain (primaryCutoff X) (W X))
      atTop (nhds 0) := by
  apply tendsto_totientTypeIMain_of_log_comparison mertens_log_six.tendsto_odd_totient_log_sq
    primaryCutoff W tendsto_primaryCutoff 5 (by norm_num)
  filter_upwards [hW] with X hWX
  have hnat : W X + 1 ≤ (primaryCutoff X + 1) ^ 5 := by
    have := primaryCutoff_inverse_bound X
    omega
  have hreal : (W X : ℝ) + 1 ≤ ((primaryCutoff X : ℝ) + 1) ^ 5 := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (W X : ℝ) + 1) hreal
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

theorem eventually_rightCutoff_le_of_primary_product_bound (W : ℕ → ℕ)
    (a : ℝ) (ha : a ≤ 1)
    (hprod : ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * W X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    ∀ᶠ X : ℕ in atTop, W X ≤ X := by
  filter_upwards [hprod, eventually_ge_atTop 1] with X hPX hX
  have hp : primaryCutoff X * W X ≤ X := by
    exact_mod_cast hPX.trans (Real.rpow_le_self_of_one_le (by exact_mod_cast hX) ha)
  exact (Nat.le_mul_of_pos_left (W X) (primaryCutoff_pos hX)).trans hp

theorem tendsto_typeITerm_primary_right_div_of_product_bound (W : ℕ → ℕ)
    (a : ℝ) (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hprod : ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * W X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    Tendsto (fun X : ℕ => typeITerm (primaryCutoff X) (W X) X / X)
      atTop (nhds 0) := by
  have hW := eventually_rightCutoff_le_of_primary_product_bound W a (by linarith) hprod
  have h := (maximal_bombieri_vinogradov.tendsto_mixed_typeI_div_sub_main
      primaryCutoff W a ha haHalf hprod).add
    (tendsto_totientTypeIMain_primary_of_right_le W hW)
  simpa only [zero_add, sub_add_cancel] using h

theorem tendsto_primary_bilinear_sub_rightCutoff_div (W : ℕ → ℕ)
    (a : ℝ) (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hprod : ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * W X : ℕ) : ℝ) ≤ (X : ℝ) ^ a) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (primaryCutoff X) (primaryCutoff X) X -
        bilinearTerm (primaryCutoff X) (W X) X) / X)
      atTop (nhds 0) := by
  have hI := tendsto_typeITerm_div_of_inputs maximal_bombieri_vinogradov
    (tendsto_totientTypeIMain_same_cutoff mertens_log_six.tendsto_odd_totient_log_sq
      primaryCutoff tendsto_primaryCutoff)
  have h := hI.sub (tendsto_typeITerm_primary_right_div_of_product_bound W a ha haHalf hprod)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1,
    eventually_rightCutoff_le_of_primary_product_bound W a (by linarith) hprod] with X hX hW
  rw [bilinearTerm_sub_eq_typeITerm_sub _ _ _ _ (primaryCutoff_le hX) hW, sub_div]

theorem tendsto_totientTypeIMain_primary_quarter :
    Tendsto (fun X : ℕ => totientTypeIMain (primaryCutoff X) (quarterCutoff X))
      atTop (nhds 0) := by
  apply tendsto_totientTypeIMain_of_log_comparison mertens_log_six.tendsto_odd_totient_log_sq
    primaryCutoff quarterCutoff tendsto_primaryCutoff 5 (by norm_num)
  filter_upwards [eventually_ge_atTop 1] with X hX
  exact log_quarterCutoff_add_one_le_five_log_primaryCutoff X hX

theorem tendsto_typeITerm_primary_quarter_div :
    Tendsto (fun X : ℕ => typeITerm (primaryCutoff X) (quarterCutoff X) X / X)
      atTop (nhds 0) := by
  have hprod : ∀ᶠ X : ℕ in atTop,
      ((primaryCutoff X * quarterCutoff X : ℕ) : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    simpa only [Nat.cast_mul] using primaryCutoff_mul_quarterCutoff_le_rpow X hX
  have h := (maximal_bombieri_vinogradov.tendsto_mixed_typeI_div_sub_main
      primaryCutoff quarterCutoff (9 / 20) (by norm_num) (by norm_num) hprod).add
    tendsto_totientTypeIMain_primary_quarter
  simpa only [zero_add, sub_add_cancel] using h

theorem tendsto_primary_bilinear_sub_quarter_div :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (primaryCutoff X) (primaryCutoff X) X -
        bilinearTerm (primaryCutoff X) (quarterCutoff X) X) / X)
      atTop (nhds 0) := by
  have hI := tendsto_typeITerm_div_of_inputs maximal_bombieri_vinogradov
    (tendsto_totientTypeIMain_same_cutoff mertens_log_six.tendsto_odd_totient_log_sq
      primaryCutoff tendsto_primaryCutoff)
  have h := hI.sub tendsto_typeITerm_primary_quarter_div
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [bilinearTerm_sub_eq_typeITerm_sub _ _ _ _ (primaryCutoff_le hX) (quarterCutoff_le hX),
    sub_div]

theorem tendsto_quarter_bilinear_sub_primeBeta_div_mul_log_pow (U : ℕ → ℕ) (k : ℕ) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (U X) (quarterCutoff X) X - bilinearPrimeBeta (U X) (quarterCutoff X) X) /
        X * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_bilinear_sub_primeBeta_bound
  apply tendsto_mul_dispersion_log_pow_of_primaryCutoff_neg_half_bound _ C 2 k
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hU : (0 : ℝ) < primaryCutoff X := by exact_mod_cast primaryCutoff_pos hX
  have hpow : (quarterCutoff X : ℝ) ^ (-1 / 2 : ℝ) ≤
      (primaryCutoff X : ℝ) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hU (by exact_mod_cast primaryCutoff_le_quarterCutoff hX)
      (by norm_num)
  rw [abs_div, abs_of_nonneg hx.le]
  calc
    _ ≤ (C * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 *
        (quarterCutoff X : ℝ) ^ (-1 / 2 : ℝ)) / X :=
      div_le_div_of_nonneg_right (hbound (U X) (quarterCutoff X) X
        (quarterCutoff_pos hX) hX) hx.le
    _ = C * (Real.log (4 * X + 4)) ^ 2 * (quarterCutoff X : ℝ) ^ (-1 / 2 : ℝ) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem tendsto_quarter_bilinear_sub_primeBeta_div (U : ℕ → ℕ) :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (U X) (quarterCutoff X) X - bilinearPrimeBeta (U X) (quarterCutoff X) X) / X)
      atTop (nhds 0) := by
  simpa using tendsto_quarter_bilinear_sub_primeBeta_div_mul_log_pow U 0

theorem tendsto_primary_bilinear_sub_quarterPrimeBeta_div :
    Tendsto (fun X : ℕ =>
      (bilinearTerm (primaryCutoff X) (primaryCutoff X) X -
        bilinearPrimeBeta (primaryCutoff X) (quarterCutoff X) X) / X)
      atTop (nhds 0) := by
  have h := tendsto_primary_bilinear_sub_quarter_div.add
    (tendsto_quarter_bilinear_sub_primeBeta_div primaryCutoff)
  simp only [add_zero] at h
  convert h using 1
  ext X
  ring

end TwinPrime.Analytic
