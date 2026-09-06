import TwinPrime.Analytic.PrimeDistribution
import TwinPrime.Analytic.EvenAsymptotics
import TwinPrime.Analytic.GrowthBounds

/-!
# The mixed correlation and its separate analytic inputs

The finite estimate separates reduced odd residue classes from the exceptional
even moduli. The smoothed Möbius/totient sum is an ordinary one-variable
arithmetic quantity; no shifted-prime lower bound is hidden in its definition.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

def truncatedWeight (U d : ℕ) : ℝ := (μ d : ℝ) * Real.log ((U : ℝ) / d)

/-- The smoothed odd Möbius/totient main coefficient. -/
def smoothedTotientSum (U : ℕ) : ℝ :=
  ∑ d ∈ range (U + 1) with Odd d, truncatedWeight U d / Nat.totient d

theorem mixedCorrelation_eq_odd_add_even (U X : ℕ) :
    mixedCorrelation U X =
      (∑ d ∈ range (U + 1) with Odd d, truncatedWeight U d *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2)) +
      ∑ d ∈ range (U + 1) with Even d, truncatedWeight U d *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2) := by
  rw [mixedCorrelation_eq_progressions]
  simpa only [truncatedWeight, Nat.not_odd_iff_even] using
    (sum_filter_add_sum_filter_not (range (U + 1)) Odd
      (fun d => (μ d : ℝ) * Real.log ((U : ℝ) / d) *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2))).symm

/-- Finite quantitative mixed estimate. The first error concerns only reduced
residue classes; the second is an unconditional bound for all even moduli. -/
theorem mixedCorrelation_error_le (U X : ℕ) :
    |mixedCorrelation U X - (X : ℝ) * smoothedTotientSum U| ≤
      2 * Real.log (U + 1) * ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q +
        (U + 1 : ℝ) * Real.log (U + 1) * evenProgressionBound X := by
  have hL : 0 ≤ Real.log (U + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) U; linarith)
  have hodd := weighted_odd_progression_error_le_of_cap U X (truncatedWeight U)
    (Real.log (U + 1)) hL (fun q hq _ => abs_moebius_log_div_le U q (mem_Icc.mp hq).2)
  have heven := weighted_even_progression_le X ((range (U + 1)).filter Even)
    (truncatedWeight U) (fun q hq => (mem_filter.mp hq).2)
  have hnorm : (∑ q ∈ range (U + 1) with Even q, |truncatedWeight U q|) ≤
      (U + 1 : ℝ) * Real.log (U + 1) := by
    calc
      _ ≤ ∑ q ∈ range (U + 1) with Even q, Real.log (U + 1) := by
        apply sum_le_sum
        intro q hq
        exact abs_moebius_log_div_le U q (by have := mem_range.mp (mem_filter.mp hq).1; omega)
      _ ≤ ∑ q ∈ range (U + 1), Real.log (U + 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hL)
      _ = _ := by simp
  have heven' := heven.trans (mul_le_mul_of_nonneg_right hnorm (evenProgressionBound_nonneg X))
  rw [mixedCorrelation_eq_odd_add_even]
  unfold smoothedTotientSum
  have htriangle := abs_add_le
    ((∑ d ∈ range (U + 1) with Odd d, truncatedWeight U d *
      ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2)) -
        (X : ℝ) * ∑ d ∈ range (U + 1) with Odd d, truncatedWeight U d / Nat.totient d)
    (∑ d ∈ range (U + 1) with Even d, truncatedWeight U d *
      ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2))
  rw [sub_add_eq_add_sub] at htriangle
  exact htriangle.trans (add_le_add hodd heven')

/-- A single error budget for the primary cutoffs. -/
theorem mixedCorrelation_error_le_primary (X : ℕ) (hX : 1 ≤ X) :
    |mixedCorrelation (primaryCutoff X) X - (X : ℝ) * smoothedTotientSum (primaryCutoff X)| ≤
      2 * Real.log (2 * X + 2) * primaryProgressionError X + evenWeightBudget X := by
  let U := primaryCutoff X
  have hU : 1 ≤ U := primaryCutoff_pos hX
  have hUX : U ≤ X := primaryCutoff_le hX
  have hUsq : U ≤ U ^ 2 := by nlinarith
  have hL : 0 ≤ Real.log (U + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) U; linarith)
  have hLog : Real.log (U + 1) ≤ Real.log (2 * X + 2) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show U + 1 ≤ 2 * X + 2 by omega)
  apply (mixedCorrelation_error_le U X).trans
  apply add_le_add
  · apply mul_le_mul (mul_le_mul_of_nonneg_left hLog (by norm_num))
      (sum_progressionMaxError_le_primary hUsq)
    · exact sum_nonneg (fun q _ => progressionMaxError_nonneg _ q)
    · have hLog0 := hL.trans hLog
      positivity
  · change (U + 1 : ℝ) * Real.log (U + 1) * evenProgressionBound X ≤
      ((U : ℝ) ^ 2 + 1) * Real.log (2 * X + 2) * evenProgressionBound X
    apply mul_le_mul_of_nonneg_right _ (evenProgressionBound_nonneg X)
    apply mul_le_mul _ hLog hL (by positivity)
    exact_mod_cast (show U + 1 ≤ U ^ 2 + 1 by omega)

/-- The mixed-correlation remainder is sublinear assuming the named distribution
input. The Möbius/totient main coefficient has not been evaluated in this theorem. -/
theorem MaximalBombieriVinogradov.tendsto_mixed_error_div (hBV : MaximalBombieriVinogradov) :
    Tendsto (fun X : ℕ => (mixedCorrelation (primaryCutoff X) X -
      (X : ℝ) * smoothedTotientSum (primaryCutoff X)) / X) atTop (nhds 0) := by
  have h := (hBV.tendsto_log_mul_sum_error_div.const_mul 2).add tendsto_evenWeightBudget_div
  simp only [mul_zero, zero_add] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with X hX
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)]
    have hb := div_le_div_of_nonneg_right (mixedCorrelation_error_le_primary X hX)
      (Nat.cast_nonneg (α := ℝ) X)
    simpa only [add_div, mul_div_assoc, mul_assoc] using hb

/-- The primary cutoff tends to infinity, so a known one-variable limit may
be applied to it without strengthening its quantifiers. -/
theorem tendsto_primaryCutoff : Tendsto primaryCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop)

/-- Evaluation of the mixed correlation from two separate classical inputs.
Neither input is proved by the finite divisor algebra. -/
theorem tendsto_mixedCorrelation_div_of_inputs (hBV : MaximalBombieriVinogradov)
    {C : ℝ} (hF : Tendsto smoothedTotientSum atTop (nhds C)) :
    Tendsto (fun X : ℕ => mixedCorrelation (primaryCutoff X) X / X) atTop (nhds C) := by
  have h := hBV.tendsto_mixed_error_div.add (hF.comp tendsto_primaryCutoff)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  dsimp only [Function.comp_def]
  field_simp
  ring

/-- Convert a normalized limit to an explicit eventual linear error budget. -/
theorem eventually_abs_sub_mul_le_of_tendsto_div (f : ℕ → ℝ) {C ε : ℝ}
    (hε : 0 < ε) (hf : Tendsto (fun X : ℕ => f X / X) atTop (nhds C)) :
    ∀ᶠ X : ℕ in atTop, |f X - C * X| ≤ ε * X := by
  have habs : Tendsto (fun X : ℕ => |f X / X - C|) atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using (hf.sub_const C).abs
  have hnear := habs.eventually (gt_mem_nhds hε)
  filter_upwards [hnear, eventually_ge_atTop 1] with X hX hX1
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have heq : f X / X - C = (f X - C * X) / X := by field_simp
  rw [heq, abs_div, abs_of_pos hx] at hX
  exact ((div_lt_iff₀ hx).mp hX).le

/-- The precise mixed-correlation row in the final error budget, still explicitly
conditional on the two classical inputs. -/
theorem eventually_mixedCorrelation_budget_of_inputs (hBV : MaximalBombieriVinogradov)
    {C : ℝ} (hC : 0 < C) (hF : Tendsto smoothedTotientSum atTop (nhds C)) :
    ∀ᶠ X : ℕ in atTop,
      |mixedCorrelation (primaryCutoff X) X - C * X| ≤ C * X / 8 := by
  simpa only [div_mul_eq_mul_div] using
    eventually_abs_sub_mul_le_of_tendsto_div _ (show 0 < C / 8 by positivity)
      (tendsto_mixedCorrelation_div_of_inputs hBV hF)

end TwinPrime.Analytic
