import TwinPrime.Analytic.AnalyticLogDerivativeBound
import TwinPrime.Analytic.ZeroFactorBounds
import TwinPrime.Analytic.ZeroFactorLogDerivative
import Mathlib.Analysis.Complex.JensenFormula

/-!
# A quantitative logarithmic derivative expansion over the actual zeros

Zeros in the closed disk of radius `5/4` are removed with their analytic
multiplicities. The outer disk has radius `3/2`; the error bound holds on
the closed unit disk at every nonzero of the original function.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

theorem norm_logDeriv_sub_zero_sum_le {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c (3 / 2))) (hfc : f c ≠ 0)
    (hM : 1 ≤ M) (hbound : ∀ w ∈ sphere c (3 / 2), ‖f w‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall c 1) (hfz : f z ≠ 0) :
    ‖logDeriv f z - (∑ᶠ u, (divisor f (closedBall c (5 / 4)) u : ℂ) / (z - u))‖ ≤
      (144 * (1 + Real.log 5 / Real.log (6 / 5))) * (1 + Real.log (M / ‖f c‖)) := by
  have hinner : closedBall c (5 / 4) ⊆ closedBall c (3 / 2) :=
    closedBall_subset_closedBall (by norm_num)
  obtain ⟨g, hg, hgn, hEq⟩ := exists_holomorphic_zero_removal hf
    isPreconnected_closedBall (mem_closedBall_self (by norm_num)) hfc
    (isCompact_closedBall c (5 / 4)) hinner
  let N := zeroFactorMultiplicity f (closedBall c (5 / 4))
  have hgball : DifferentiableOn ℂ g (ball c (5 / 4)) :=
    hg.differentiableOn.mono (ball_subset_closedBall.trans hinner)
  have hgnball : ∀ w ∈ ball c (5 / 4), g w ≠ 0 :=
    fun w hw => hgn w (ball_subset_closedBall hw)
  have hgbound : ∀ w ∈ ball c (5 / 4), ‖g w‖ ≤ M * 4 ^ N := by
    intro w hw
    exact norm_zero_removal_quotient_le_on_closedBall c hf hg M hEq hbound w
      (hinner (ball_subset_closedBall hw))
  have hgz := norm_logDerivative_le_of_nonvanishing_on_ball hgball hgnball hgbound z hz
  have hzc : z ∈ ball c (3 / 2) := closedBall_subset_ball (by norm_num) hz
  have hlogEq := logDeriv_eq_zeroFactor_sum_add isOpen_ball
    (hf.differentiableOn.mono ball_subset_closedBall)
    (hg.differentiableOn.mono ball_subset_closedBall) (isCompact_closedBall c (5 / 4))
    (fun w hw => hEq w (ball_subset_closedBall hw)) z hzc hfz
  rw [hlogEq, add_sub_cancel_left]
  change ‖deriv g z / g z‖ ≤ _
  apply hgz.trans
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr
    (hgn c (mem_closedBall_self (by norm_num)))
  have hcenter : ‖f c‖ ≤ (5 / 4 : ℝ) ^ N * ‖g c‖ := by
    have hc := zero_removal_center_lower c hf (hEq c (mem_closedBall_self (by norm_num)))
    have hc' := (div_le_iff₀ (by positivity : 0 < (5 / 4 : ℝ) ^ N)).mp hc
    simpa only [mul_comm] using hc'
  have hbudget := zero_removal_log_budget_le (M := M)
    (norm_pos_iff.mpr hfc) hgc (by linarith) N hcenter
  have hj := AnalyticOnNhd.sum_divisor_le (c := c) (r := (5 / 4 : ℝ))
    (R := (3 / 2 : ℝ)) (M := M) (by norm_num) (by norm_num) hM
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using hf) hfc
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using hbound)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at hj
  norm_num at hj
  have hN : (N : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (6 / 5) := by
    rw [show (N : ℝ) = ((∑ᶠ u, divisor f (closedBall c (5 / 4)) u : ℤ) : ℝ) from
      zeroFactorMultiplicity_cast (hf.mono hinner) (isCompact_closedBall _ _)]
    exact hj
  exact (mul_le_mul_of_nonneg_left hbudget (by norm_num)).trans
    (zero_removal_log_budget_le_of_jensen N hN)

end TwinPrime.Analytic
