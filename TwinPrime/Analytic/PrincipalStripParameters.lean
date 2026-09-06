import TwinPrime.Analytic.SiegelWalfiszStripBudget
import TwinPrime.Analytic.SmoothedPrincipalContour

/-!
# Principal bounds at the common contour width

At conductor one the primitive logarithmic width is twice the zeta width.
The two halvings in the common evaluation width therefore fit inside the
proved principal zero-free rectangle. The principal norm budget is at
most twice the conductor-one primitive budget.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem primitiveLogZeroFreeWidth_one_eq_twice_zeta (H : ℝ) :
    primitiveLogZeroFreeWidth 1 H = 2 * zetaLogZeroFreeWidth H := by
  unfold primitiveLogZeroFreeWidth zetaLogZeroFreeWidth
  simp only [Nat.cast_one, Real.log_one, add_zero]
  simp only [one_div, mul_inv_rev]
  ring

theorem common_principal_width_le_zeta (ε d H : ℝ) :
    2 * (primitiveZeroFreeRectangleWidth ε d 1 (H + 2) / 2) ≤
      zetaLogZeroFreeWidth (H + 2) := by
  have hw := twice_primitiveZeroFreeRectangleWidth_le_log_width ε d 1 (H + 2)
  rw [primitiveLogZeroFreeWidth_one_eq_twice_zeta] at hw
  linarith

theorem zetaStripBudget_le_twice_primitive (H δ : ℝ) (hδ : 0 < δ) :
    zetaStripLogDerivativeBudget H δ ≤ 2 * primitiveStripLogDerivativeBudget 1 H δ := by
  have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have he : 2 * primitiveStripLogDerivativeBudget 1 H δ - zetaStripLogDerivativeBudget H δ =
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) * (1 + Real.log 16) +
        (Real.log 16 / Real.log (6 / 5)) / δ := by
    unfold primitiveStripLogDerivativeBudget zetaStripLogDerivativeBudget
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero]
    ring
  have hn : 0 ≤ 2 * primitiveStripLogDerivativeBudget 1 H δ - zetaStripLogDerivativeBudget H δ := by
    rw [he]
    positivity
  linarith

theorem principal_common_strip_width_and_budget (B K d L : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) (hL : 1 ≤ L) :
    siegelWalfiszStripWidthConstant B K d * L ^ (-(1 / 2 : ℝ)) ≤
        primitiveZeroFreeRectangleWidth (1 / (2 * B)) d 1 (L ^ K + 2) / 2 ∧
      zetaStripLogDerivativeBudget (L ^ K)
          (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d 1 (L ^ K + 2) / 2) ≤
        (2 * siegelWalfiszStripBudgetConstant B K d) * L := by
  have hqL : ((1 : ℕ) : ℝ) ≤ L ^ B := by simpa using Real.one_le_rpow hL hB.le
  have hw := primitiveZeroFreeRectangleWidth_pos (1 / (2 * B)) d hd 1 (L ^ K + 2)
  refine ⟨siegelWalfiszStripWidthConstant_mul_rpow_le B K d L hB hK hd hL 1 le_rfl hqL, ?_⟩
  apply (zetaStripBudget_le_twice_primitive (L ^ K)
    (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d 1 (L ^ K + 2) / 2) (by positivity)).trans
  have hb := mul_le_mul_of_nonneg_left
    (siegelWalfiszStripBudgetConstant_bound B K d L hB hK hd hL 1 le_rfl hqL)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using hb

/-- The principal contour can use the same parameterized evaluation
width as the primitive-character family, for any positive `d`. -/
theorem norm_weighted_vonMangoldt_sub_half_le_at_common_width (ε d x c H : ℝ)
    (hd : 0 < d) (hx : 1 ≤ x) (hc : 1 < c) (hcu : c ≤ 2) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      ((x / 2 : ℝ) : ℂ)‖ ≤
        smoothedPrincipalContourBudget x
          (1 - primitiveZeroFreeRectangleWidth ε d 1 (H + 2) / 2) c H
          (zetaStripLogDerivativeBudget H (primitiveZeroFreeRectangleWidth ε d 1 (H + 2) / 2)) + 1 := by
  have hw := primitiveZeroFreeRectangleWidth_pos ε d hd 1 (H + 2)
  have hwu := primitiveZeroFreeRectangleWidth_le_one_thirtysecond ε d 1 (H + 2)
  have hcontour := norm_weighted_vonMangoldt_sub_pole_le_of_width x c H
    (primitiveZeroFreeRectangleWidth ε d 1 (H + 2) / 2) hx hc hcu hH
    (by positivity) (by linarith) (common_principal_width_le_zeta ε d H)
  have hpole := norm_mellinPoleWeight_one_div_sub_half_le x hx
  have hn := norm_add_le
    (weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x - mellinPoleWeight (1 / x))
    (mellinPoleWeight (1 / x) - ((x / 2 : ℝ) : ℂ))
  rw [sub_add_sub_cancel] at hn
  exact hn.trans (_root_.add_le_add hcontour hpole)

end TwinPrime.Analytic
