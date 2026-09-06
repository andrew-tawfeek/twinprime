import TwinPrime.Analytic.WideLocalLogDerivativeExpansion
import TwinPrime.Analytic.LFunctionZeroCount
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Primitive L-function zero expansions on radius 17/16

The actual divisor disk and conductor/height growth budget are unchanged.
The wider evaluation disk has remainder constant `288`. Values left of
one retain an explicit nonvanishing hypothesis.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

theorem wide_norm_logDeriv_LFunction_sub_zero_sum_le {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c : ℂ) (hc : c.re = 2) (z : ℂ) (hz : z ∈ closedBall c (17 / 16))
    (hfz : DirichletCharacter.LFunction χ z ≠ 0) :
    ‖logDeriv (DirichletCharacter.LFunction χ) z -
        (∑ᶠ u, (divisor (DirichletCharacter.LFunction χ)
          (closedBall c (5 / 4)) u : ℂ) / (z - u))‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log q + Real.log (‖c‖ + 2)) := by
  let M : ℝ := 4 * (q : ℝ) ^ 2 * (‖c‖ + 2)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (norm_nonneg c)]
  have hcenter : 1 / 4 ≤ ‖DirichletCharacter.LFunction χ c‖ :=
    one_quarter_le_norm_LFunction χ c (by rw [hc])
  have hcenter0 : 0 < ‖DirichletCharacter.LFunction χ c‖ := by linarith
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (3 / 2)) :=
    fun w _ => (DirichletCharacter.differentiable_LFunction
      (primitive_character_ne_one hq χ hχ)).analyticAt w
  have hbound : ∀ w ∈ sphere c (3 / 2), ‖DirichletCharacter.LFunction χ w‖ ≤ M := by
    intro w hw
    have ht := norm_LFunction_le_on_closedBall hq χ hχ c (3 / 2)
      (by rw [hc]; norm_num) w (sphere_subset_closedBall hw)
    have ht' : ‖DirichletCharacter.LFunction χ w‖ ≤
        primitiveLFunctionGrowthBudget q (1 / 2) (‖c‖ + 3 / 2) := by
      simpa only [hc, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using ht
    exact ht'.trans (primitiveLFunctionGrowthBudget_half_le q hq c)
  have he := wide_norm_logDeriv_sub_zero_sum_le hf (norm_pos_iff.mp hcenter0) hM hbound z hz hfz
  apply he.trans
  have hratio : M / ‖DirichletCharacter.LFunction χ c‖ ≤
      16 * (q : ℝ) ^ 2 * (‖c‖ + 2) := by
    calc
      _ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hcenter
      _ = _ := by dsimp [M]; ring
  have hH : 0 < ‖c‖ + 2 := by positivity
  have hlog : Real.log (M / ‖DirichletCharacter.LFunction χ c‖) ≤
      Real.log 16 + 2 * Real.log q + Real.log (‖c‖ + 2) := by
    calc
      _ ≤ Real.log (16 * (q : ℝ) ^ 2 * (‖c‖ + 2)) :=
        Real.log_le_log (div_pos (by linarith) hcenter0) hratio
      _ = _ := by
        rw [Real.log_mul (by positivity) hH.ne',
          Real.log_mul (by norm_num) (pow_ne_zero 2 hq0.ne'), Real.log_pow]
        norm_num
  apply mul_le_mul_of_nonneg_left (by linarith)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  positivity

/-- On Re(z)≥1, qualitative nonvanishing discharges the evaluation condition. -/
theorem wide_norm_logDeriv_LFunction_sub_zero_sum_le_of_one_le_re {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (c : ℂ) (hc : c.re = 2) (z : ℂ) (hz : z ∈ closedBall c (17 / 16))
    (hre : 1 ≤ z.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) z -
        (∑ᶠ u, (divisor (DirichletCharacter.LFunction χ)
          (closedBall c (5 / 4)) u : ℂ) / (z - u))‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log q + Real.log (‖c‖ + 2)) := by
  exact wide_norm_logDeriv_LFunction_sub_zero_sum_le hq χ hχ c hc z hz
    (χ.LFunction_ne_zero_of_one_le_re (.inl (primitive_character_ne_one hq χ hχ)) hre)

end TwinPrime.Analytic
