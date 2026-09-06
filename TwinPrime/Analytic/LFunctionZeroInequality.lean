import TwinPrime.Analytic.LFunctionLocalExpansion
import TwinPrime.Analytic.LFunctionZeroSigns

/-!

# One-sided local L-function logarithmic-derivative bounds

The proved expansion over the actual divisor combines with the sign of
each zero contribution to give an upper bound for the negative logarithmic
derivative. A selected actual zero contributes its reciprocal explicitly.
-/

noncomputable section

open Metric

namespace TwinPrime.Analytic

def primitiveLFunctionLogBudget (q : ℕ) (t : ℝ) : ℝ :=
  (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
    (1 + Real.log 16 + 2 * Real.log q + Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2))

theorem primitiveLFunctionLogBudget_nonneg (q : ℕ) (t : ℝ) :
    0 ≤ primitiveLFunctionLogBudget q t := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hq := Real.log_natCast_nonneg q
  have hH : 0 ≤ Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) :=
    Real.log_nonneg (by have := norm_nonneg ((2 : ℂ) + Complex.I * t); linarith)
  unfold primitiveLFunctionLogBudget
  positivity

theorem primitiveLFunctionLogBudget_mono_conductor (d q : ℕ)
    (hd : 1 ≤ d) (hdq : d ≤ q) (t : ℝ) :
    primitiveLFunctionLogBudget d t ≤ primitiveLFunctionLogBudget q t := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : Real.log (d : ℝ) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast (show 0 < d by omega)) (by exact_mod_cast hdq)
  unfold primitiveLFunctionLogBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- The stated real range lies in the closed unit disk about `2+it`. -/
theorem sigma_add_I_mul_mem_local_disk (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (σ : ℂ) + Complex.I * t ∈ closedBall ((2 : ℂ) + Complex.I * t) 1 := by
  have heq : (σ : ℂ) + Complex.I * t - ((2 : ℂ) + Complex.I * t) =
      ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [mem_closedBall_iff_norm, heq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The whole actual zero sum appears with a negative sign. -/
theorem neg_logDerivative_LFunction_re_le_budget_sub_zeroSum {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * t) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * t)).re ≤
        primitiveLFunctionLogBudget q t -
          (localLFunctionZeroSum χ ((2 : ℂ) + Complex.I * t)
            ((σ : ℂ) + Complex.I * t)).re := by
  let c : ℂ := (2 : ℂ) + Complex.I * t
  let z : ℂ := (σ : ℂ) + Complex.I * t
  have hc : c.re = 2 := by simp [c]
  have hz : z ∈ closedBall c 1 := sigma_add_I_mul_mem_local_disk σ t hσ hσu
  have hzr : 1 ≤ z.re := by simpa [z] using hσ.le
  have hb := norm_logDeriv_LFunction_sub_zero_sum_le_of_one_le_re hq χ hχ c hc z hz hzr
  change ‖logDeriv (DirichletCharacter.LFunction χ) z - localLFunctionZeroSum χ c z‖ ≤
    primitiveLFunctionLogBudget q t at hb
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (logDeriv (DirichletCharacter.LFunction χ) z - localLFunctionZeroSum χ c z))).1
  simp only [Complex.sub_re] at hr
  change (-deriv (DirichletCharacter.LFunction χ) z /
    DirichletCharacter.LFunction χ z).re ≤
      primitiveLFunctionLogBudget q t - (localLFunctionZeroSum χ c z).re
  rw [neg_div, Complex.neg_re]
  change -(logDeriv (DirichletCharacter.LFunction χ) z).re ≤ _
  linarith

/-- Dropping the nonnegative actual zero sum leaves a conductor/height budget. -/
theorem neg_logDerivative_LFunction_re_le_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * t) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * t)).re ≤
        primitiveLFunctionLogBudget q t := by
  apply (neg_logDerivative_LFunction_re_le_budget_sub_zeroSum hq χ hχ σ t hσ hσu).trans
  apply sub_le_self
  exact localLFunctionZeroSum_re_nonneg hq χ hχ _ _ (by simpa using hσ)

/-- A selected actual zero gives the reciprocal term needed by the
three-four-one zero-exclusion argument. -/
theorem neg_logDerivative_LFunction_re_le_budget_sub_one_div_of_zero {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β t σ : ℝ) (hβ : 3 / 4 ≤ β) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * t) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * t)).re ≤
        primitiveLFunctionLogBudget q t - 1 / (σ - β) := by
  apply (neg_logDerivative_LFunction_re_le_budget_sub_zeroSum hq χ hχ σ t hσ hσu).trans
  exact sub_le_sub_left
    (one_div_sub_le_localLFunctionZeroSum_re_of_zero hq χ hχ β t σ hβ hσ hzero) _

end TwinPrime.Analytic
