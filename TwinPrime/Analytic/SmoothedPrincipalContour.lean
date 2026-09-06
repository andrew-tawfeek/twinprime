import TwinPrime.Analytic.PrincipalMellinInversion

/-!
# The principal smoothed contour estimate

The exact pole inverse is separated before shifting the holomorphic
regularized-zeta integrand. Its independent zero-free rectangle supplies
all nonvanishing and norm hypotheses. The final bound centers the actual
smoothed Mangoldt sum at `x/2`, with the pole correction at most one.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

theorem norm_weighted_vonMangoldt_sub_pole_sub_vertical_le (x c H : ℝ)
    (hx : 0 < x) (hc : 1 < c) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
        mellinPoleWeight (1 / x) - (1 / (2 * Real.pi) : ℝ) •
          mellinVerticalSegment x negativeRegularizedZetaLogDerivative c H‖ ≤
      x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / (Real.pi * H) := by
  rw [weighted_vonMangoldt_sum_sub_pole_eq_contour_integral x c hx hc]
  have ht := norm_integral_sub_intervalIntegral_le_of_inv_sq_bound
    (fun t : ℝ => mellinContourIntegrand x negativeRegularizedZetaLogDerivative ((c : ℂ) + t * I))
    (integrable_regularizedZeta_contour_integrand x c hx hc) H
    (x ^ c * (mangoldtDirichletMass c + 1 / (c - 1))) hH (by
      intro t ht
      exact norm_regularizedZeta_mellin_integrand_le_inv_sq x c t hx hc
        (by intro he; simp only [he, abs_zero] at ht; linarith))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (2 * (x ^ c * (mangoldtDirichletMass c + 1 / (c - 1))) / H) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

def smoothedPrincipalContourBudget (x a c H M : ℝ) : ℝ :=
  x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / (Real.pi * H) +
    (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2)

theorem norm_weighted_vonMangoldt_sub_pole_le_contour_budget (x a c H M : ℝ)
    (hx : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c) (hc : 1 < c)
    (hH : 0 < H) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ negativeRegularizedZetaLogDerivative (Icc a c ×ℂ Icc (-H) H))
    (hF : ∀ s ∈ Icc a c ×ℂ Icc (-H) H, ‖negativeRegularizedZetaLogDerivative s‖ ≤ M) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      mellinPoleWeight (1 / x)‖ ≤ smoothedPrincipalContourBudget x a c H M := by
  have htail := norm_weighted_vonMangoldt_sub_pole_sub_vertical_le x c H (by linarith) hc hH
  have hrect := norm_mellinVerticalSegment_right_le x hx negativeRegularizedZetaLogDerivative
    a c H M ha hac hH hM hd hF
  let S := weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
    mellinPoleWeight (1 / x)
  let V := (1 / (2 * Real.pi) : ℝ) • mellinVerticalSegment x negativeRegularizedZetaLogDerivative c H
  have hV : ‖V‖ ≤ (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2) := by
    dsimp only [V]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left hrect (by positivity)
  have hsum := norm_add_le (S - V) V
  rw [sub_add_cancel] at hsum
  change ‖S - V‖ ≤ _ at htail
  change ‖S‖ ≤ _
  unfold smoothedPrincipalContourBudget
  linarith

/-- Only the numerical width condition is required; zeta's nonvanishing
and the contour hypotheses are proved independently. -/
theorem norm_weighted_vonMangoldt_sub_pole_le_of_width (x c H δ : ℝ)
    (hx : 1 ≤ x) (hc : 1 < c) (hcu : c ≤ 2) (hH : 0 < H)
    (hδ : 0 < δ) (hδu : δ ≤ 1 / 16) (hwidth : 2 * δ ≤ zetaLogZeroFreeWidth (H + 2)) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      mellinPoleWeight (1 / x)‖ ≤
        smoothedPrincipalContourBudget x (1 - δ) c H (zetaStripLogDerivativeBudget H δ) := by
  have hfree (u : ℂ) (hu : 1 - 2 * δ ≤ u.re) (hui : |u.im| ≤ H + 2) :
      regularizedRiemannZeta u ≠ 0 :=
    regularizedRiemannZeta_ne_zero_on_rectangle (H + 2) (by linarith) u (by linarith) hui
  have hnonzero (s : ℂ) (hs : s ∈ Icc (1 - δ) c ×ℂ Icc (-H) H) :
      regularizedRiemannZeta s ≠ 0 :=
    hfree s (by linarith [hs.1.1]) (by have hh := abs_le.mpr hs.2; linarith)
  have hf := differentiable_regularizedRiemannZeta
  have hd : DifferentiableOn ℂ negativeRegularizedZetaLogDerivative
      (Icc (1 - δ) c ×ℂ Icc (-H) H) :=
    hf.deriv.neg.differentiableOn.div hf.differentiableOn hnonzero
  have hbound (s : ℂ) (hs : s ∈ Icc (1 - δ) c ×ℂ Icc (-H) H) :
      ‖negativeRegularizedZetaLogDerivative s‖ ≤ zetaStripLogDerivativeBudget H δ := by
    rw [negativeRegularizedZetaLogDerivative, neg_div, norm_neg]
    exact norm_logDeriv_regularizedZeta_le_of_zero_free_rectangle H δ hδ hδu hfree s
      hs.1.1 (hs.1.2.trans hcu) (abs_le.mpr hs.2)
  have hM : 0 ≤ zetaStripLogDerivativeBudget H δ :=
    (norm_nonneg (negativeRegularizedZetaLogDerivative 1)).trans (hbound 1 (by
      change (1 : ℂ).re ∈ Icc (1 - δ) c ∧ (1 : ℂ).im ∈ Icc (-H) H
      norm_num only [one_re, one_im, mem_Icc]
      constructor <;> constructor <;> linarith))
  exact norm_weighted_vonMangoldt_sub_pole_le_contour_budget x (1 - δ) c H
    (zetaStripLogDerivativeBudget H δ) hx (by linarith) (by linarith) hc hH hM hd hbound

theorem norm_weighted_vonMangoldt_sub_pole_le (x c H : ℝ)
    (hx : 1 ≤ x) (hc : 1 < c) (hcu : c ≤ 2) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      mellinPoleWeight (1 / x)‖ ≤
        smoothedPrincipalContourBudget x (1 - zetaEvaluationWidth H) c H
          (zetaStripLogDerivativeBudget H (zetaEvaluationWidth H)) := by
  apply norm_weighted_vonMangoldt_sub_pole_le_of_width x c H (zetaEvaluationWidth H)
    hx hc hcu hH (zetaEvaluationWidth_pos H) (min_le_left _ _)
  have h := min_le_right (1 / 16 : ℝ) (zetaLogZeroFreeWidth (H + 2) / 2)
  change 2 * min (1 / 16) (zetaLogZeroFreeWidth (H + 2) / 2) ≤ _
  linarith

/-- The actual centered principal estimate retains a bounded correction
from the exact pole inverse. No distribution premise is assumed. -/
theorem norm_weighted_vonMangoldt_sub_half_le (x c H : ℝ)
    (hx : 1 ≤ x) (hc : 1 < c) (hcu : c ≤ 2) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
      ((x / 2 : ℝ) : ℂ)‖ ≤
        smoothedPrincipalContourBudget x (1 - zetaEvaluationWidth H) c H
          (zetaStripLogDerivativeBudget H (zetaEvaluationWidth H)) + 1 := by
  have hcontour := norm_weighted_vonMangoldt_sub_pole_le x c H hx hc hcu hH
  have hpole := norm_mellinPoleWeight_one_div_sub_half_le x hx
  have hn := norm_add_le
    (weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x - mellinPoleWeight (1 / x))
    (mellinPoleWeight (1 / x) - ((x / 2 : ℝ) : ℂ))
  rw [sub_add_sub_cancel] at hn
  exact hn.trans (_root_.add_le_add hcontour hpole)

end TwinPrime.Analytic
