import TwinPrime.Analytic.WideLFunctionLocalExpansion
import TwinPrime.Analytic.WideZetaLocalExpansion
import TwinPrime.Analytic.ZeroSumNorm
import TwinPrime.Analytic.ZeroFreeRectangle

/-!
# Complex norm bounds in zero-free strips

The widened local expansion reaches left of one. A rectangle that extends
two height units and twice the evaluation width separates every actual
local zero. Jensen's multiplicity count then bounds the full complex
logarithmic derivative, not only its real part.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

def primitiveStripLogDerivativeBudget (q : ℕ) (H δ : ℝ) : ℝ :=
  (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
      (1 + Real.log 16 + 2 * Real.log q + Real.log (H + 4)) +
    ((Real.log 16 + 2 * Real.log q + Real.log (H + 4)) / Real.log (6 / 5)) / δ

def zetaStripLogDerivativeBudget (H δ : ℝ) : ℝ :=
  (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
      (1 + Real.log 16 + 2 * Real.log (H + 4)) +
    ((Real.log 16 + 2 * Real.log (H + 4)) / Real.log (6 / 5)) / δ

theorem norm_two_add_I_im_le (H : ℝ) (s : ℂ) (hs : |s.im| ≤ H) :
    ‖(2 : ℂ) + Complex.I * s.im‖ ≤ H + 2 := by
  have h := norm_add_le (2 : ℂ) (Complex.I * s.im)
  norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  linarith

theorem mem_wide_center_disk_of_re_bounds (s : ℂ) (δ : ℝ)
    (hδ : δ ≤ 1 / 16) (hs : 1 - δ ≤ s.re) (hs2 : s.re ≤ 2) :
    s ∈ closedBall ((2 : ℂ) + Complex.I * s.im) (17 / 16) := by
  have he : s - ((2 : ℂ) + Complex.I * s.im) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [mem_closedBall_iff_norm, he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The rectangle hypothesis controls the actual function throughout the
larger rectangle; no information about formal or chosen zero lists is used. -/
theorem norm_logDeriv_LFunction_le_of_zero_free_rectangle {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H δ : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1 / 16)
    (hfree : ∀ u : ℂ, 1 - 2 * δ ≤ u.re → |u.im| ≤ H + 2 →
      DirichletCharacter.LFunction χ u ≠ 0)
    (s : ℂ) (hs : 1 - δ ≤ s.re) (hs2 : s.re ≤ 2) (hsim : |s.im| ≤ H) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      primitiveStripLogDerivativeBudget q H δ := by
  let c : ℂ := (2 : ℂ) + Complex.I * s.im
  let Z : ℂ := ∑ᶠ u, (divisor (DirichletCharacter.LFunction χ)
    (closedBall c (5 / 4)) u : ℂ) / (s - u)
  have hc : c.re = 2 := by simp [c]
  have hci : |c.im| ≤ H := by simpa [c] using hsim
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (5 / 4)) :=
    fun u _ => (DirichletCharacter.differentiable_LFunction
      (primitive_character_ne_one hq χ hχ)).analyticAt u
  have hrem := wide_norm_logDeriv_LFunction_sub_zero_sum_le hq χ hχ c hc s
    (mem_wide_center_disk_of_re_bounds s δ hδu hs hs2)
    (hfree s (by linarith) (by linarith))
  have hsum := norm_divisor_zero_sum_le_of_zero_free_rectangle c s δ H hδ ha hci hs hfree
  have hcount := sum_divisor_LFunction_le_log_conductor_height hq χ hχ c hc
  have hlog : Real.log (‖c‖ + 2) ≤ Real.log (H + 4) :=
    Real.log_le_log (by positivity) (by have := norm_two_add_I_im_le H s hsim; dsimp [c]; linarith)
  have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hfactor : 0 ≤ (288 * (1 + Real.log 5 / Real.log (6 / 5)) : ℝ) := by positivity
  have hZ : ‖Z‖ ≤
      ((Real.log 16 + 2 * Real.log q + Real.log (H + 4)) / Real.log (6 / 5)) / δ := by
    apply hsum.trans
    apply div_le_div_of_nonneg_right _ hδ.le
    exact hcount.trans (div_le_div_of_nonneg_right (by linarith) h65.le)
  have hR : ‖logDeriv (DirichletCharacter.LFunction χ) s - Z‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log q + Real.log (H + 4)) :=
    hrem.trans (mul_le_mul_of_nonneg_left (by linarith) hfactor)
  have ht := norm_add_le (logDeriv (DirichletCharacter.LFunction χ) s - Z) Z
  rw [sub_add_cancel] at ht
  unfold primitiveStripLogDerivativeBudget
  linarith

theorem norm_logDeriv_regularizedZeta_le_of_zero_free_rectangle
    (H δ : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1 / 16)
    (hfree : ∀ u : ℂ, 1 - 2 * δ ≤ u.re → |u.im| ≤ H + 2 →
      regularizedRiemannZeta u ≠ 0)
    (s : ℂ) (hs : 1 - δ ≤ s.re) (hs2 : s.re ≤ 2) (hsim : |s.im| ≤ H) :
    ‖logDeriv regularizedRiemannZeta s‖ ≤ zetaStripLogDerivativeBudget H δ := by
  let c : ℂ := (2 : ℂ) + Complex.I * s.im
  let Z : ℂ := localZetaZeroSum c s
  have hc : c.re = 2 := by simp [c]
  have hci : |c.im| ≤ H := by simpa [c] using hsim
  have ha : AnalyticOnNhd ℂ regularizedRiemannZeta (closedBall c (5 / 4)) :=
    fun u _ => differentiable_regularizedRiemannZeta.analyticAt u
  have hrem := wide_norm_logDeriv_regularizedZeta_sub_zero_sum_le c hc s
    (mem_wide_center_disk_of_re_bounds s δ hδu hs hs2)
    (hfree s (by linarith) (by linarith))
  have hsum := norm_divisor_zero_sum_le_of_zero_free_rectangle c s δ H hδ ha hci hs hfree
  have hcount := sum_divisor_regularizedZeta_le_log_height c hc
  have hlog : Real.log (‖c‖ + 2) ≤ Real.log (H + 4) :=
    Real.log_le_log (by positivity) (by have := norm_two_add_I_im_le H s hsim; dsimp [c]; linarith)
  have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hfactor : 0 ≤ (288 * (1 + Real.log 5 / Real.log (6 / 5)) : ℝ) := by positivity
  have hZ : ‖Z‖ ≤
      ((Real.log 16 + 2 * Real.log (H + 4)) / Real.log (6 / 5)) / δ := by
    apply hsum.trans
    apply div_le_div_of_nonneg_right _ hδ.le
    exact hcount.trans (div_le_div_of_nonneg_right (by linarith) h65.le)
  have hR : ‖logDeriv regularizedRiemannZeta s - Z‖ ≤
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (H + 4)) :=
    hrem.trans (mul_le_mul_of_nonneg_left (by linarith) hfactor)
  have ht := norm_add_le (logDeriv regularizedRiemannZeta s - Z) Z
  rw [sub_add_cancel] at ht
  unfold zetaStripLogDerivativeBudget
  linarith

/-- The strip norm bound with nonvanishing discharged by the actual
uniform Siegel theorem. The same positive `d` works for all heights. -/
theorem exists_uniform_LFunction_logDeriv_strip_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ (q : ℕ) [NeZero q], 1 < q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ (H : ℝ), 0 ≤ H →
        ∀ s : ℂ,
          1 - primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2 ≤ s.re →
          s.re ≤ 2 → |s.im| ≤ H →
            ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
              primitiveStripLogDerivativeBudget q H
                (primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2) := by
  obtain ⟨d, hd, hfree⟩ := exists_LFunction_zero_free_rectangle ε hε
  refine ⟨d, hd, ?_⟩
  intro q _ hq χ hχ H hH s hs hs2 hsim
  have hwpos := primitiveZeroFreeRectangleWidth_pos ε d hd q (H + 2)
  have hwle := primitiveZeroFreeRectangleWidth_le_one_thirtysecond ε d q (H + 2)
  apply norm_logDeriv_LFunction_le_of_zero_free_rectangle hq χ hχ H
    (primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2) (by positivity) (by linarith)
    _ s hs hs2 hsim
  intro u hu hui
  exact hfree q hq χ hχ (H + 2) (by linarith) u (by linarith) hui

def zetaEvaluationWidth (H : ℝ) : ℝ :=
  min (1 / 16) (zetaLogZeroFreeWidth (H + 2) / 2)

theorem zetaEvaluationWidth_pos (H : ℝ) : 0 < zetaEvaluationWidth H := by
  have hw := zetaLogZeroFreeWidth_pos (H + 2)
  unfold zetaEvaluationWidth
  positivity

/-- The regularized principal case uses its own proved exception-free
region, including its nonzero value at one. -/
theorem norm_logDeriv_regularizedZeta_le_in_strip (H : ℝ) (hH : 0 ≤ H)
    (s : ℂ) (hs : 1 - zetaEvaluationWidth H ≤ s.re)
    (hs2 : s.re ≤ 2) (hsim : |s.im| ≤ H) :
    ‖logDeriv regularizedRiemannZeta s‖ ≤
      zetaStripLogDerivativeBudget H (zetaEvaluationWidth H) := by
  have hδu : zetaEvaluationWidth H ≤ 1 / 16 := min_le_left _ _
  have hδw : zetaEvaluationWidth H ≤ zetaLogZeroFreeWidth (H + 2) / 2 := min_le_right _ _
  apply norm_logDeriv_regularizedZeta_le_of_zero_free_rectangle H
    (zetaEvaluationWidth H) (zetaEvaluationWidth_pos H) hδu _ s hs hs2 hsim
  intro u hu hui
  exact regularizedRiemannZeta_ne_zero_on_rectangle (H + 2) (by linarith) u
    (by linarith) hui

end TwinPrime.Analytic
