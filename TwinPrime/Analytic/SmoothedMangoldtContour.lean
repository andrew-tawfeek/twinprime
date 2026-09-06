import TwinPrime.Analytic.MangoldtMellinInversion
import TwinPrime.Analytic.MellinRectangle
import TwinPrime.Analytic.MellinTruncation
import TwinPrime.Analytic.LogDerivativeStrip

/-!
# Actual smoothed Mangoldt sums and quantitative contours

The inversion theorem and the two tails are combined with a finite
rectangle shift. For primitive nonprincipal characters the zero-free
rectangle supplies both holomorphy and the full complex norm bound.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

def negativeLFunctionLogDerivative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

theorem one_div_cpow_neg_eq (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ((1 / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg, inv_inv]

theorem mellinInv_one_div_eq_contour_integral (x : ℝ) (hx : 0 < x)
    (c : ℝ) (F : ℂ → ℂ) :
    mellinInv c (fun s => F s * mellinRampKernel s) (1 / x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, mellinContourIntegrand x F ((c : ℂ) + t * I) := by
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul, one_div_cpow_neg_eq x hx]
  unfold mellinContourIntegrand
  ring

theorem integrable_mangoldt_contour_integrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      mellinContourIntegrand x (negativeLFunctionLogDerivative χ) ((c : ℂ) + t * I)) := by
  apply (integrable_mangoldt_mellinRamp_integrand χ c hc (1 / x) (by positivity)).congr
  filter_upwards [] with t
  rw [one_div_cpow_neg_eq x hx]
  unfold mellinContourIntegrand negativeLFunctionLogDerivative
  ring

/-- Truncation of the actual inverse Mellin integral, including both tails. -/
theorem norm_weighted_mangoldt_sum_sub_vertical_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x c H : ℝ)
    (hx : 0 < x) (hc : 1 < c) (hH : 0 < H) :
    ‖weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x -
        (1 / (2 * Real.pi) : ℝ) •
          mellinVerticalSegment x (negativeLFunctionLogDerivative χ) c H‖ ≤
      x ^ c * mangoldtDirichletMass c / (Real.pi * H) := by
  rw [weighted_mangoldt_sum_eq_mellinInv χ c hc x hx]
  change ‖mellinInv c (fun s => negativeLFunctionLogDerivative χ s * mellinRampKernel s) (1 / x) - _‖ ≤ _
  rw [mellinInv_one_div_eq_contour_integral x hx c]
  have ht := norm_integral_sub_intervalIntegral_le_of_inv_sq_bound
    (fun t : ℝ => mellinContourIntegrand x (negativeLFunctionLogDerivative χ) ((c : ℂ) + t * I))
    (integrable_mangoldt_contour_integrand χ x c hx hc) H
    (x ^ c * mangoldtDirichletMass c) hH (by
      intro t ht
      exact norm_mangoldt_mellin_integrand_le_inv_sq χ x c t hx hc
        (by intro he; simp only [he, abs_zero] at ht; linarith))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * (x ^ c * mangoldtDirichletMass c) / H) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

def smoothedMangoldtContourBudget (x a c H M : ℝ) : ℝ :=
  x ^ c * mangoldtDirichletMass c / (Real.pi * H) +
    (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2)

theorem norm_weighted_mangoldt_sum_le_contour_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x a c H M : ℝ)
    (hx : 1 ≤ x) (ha : 0 < a) (hac : a ≤ c) (hc : 1 < c)
    (hH : 0 < H) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ (negativeLFunctionLogDerivative χ)
      (Icc a c ×ℂ Icc (-H) H))
    (hF : ∀ s ∈ Icc a c ×ℂ Icc (-H) H, ‖negativeLFunctionLogDerivative χ s‖ ≤ M) :
    ‖weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x‖ ≤
      smoothedMangoldtContourBudget x a c H M := by
  have htail := norm_weighted_mangoldt_sum_sub_vertical_le χ x c H (by linarith) hc hH
  have hrect := norm_mellinVerticalSegment_right_le x hx (negativeLFunctionLogDerivative χ)
    a c H M ha hac hH hM hd hF
  let S := weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x
  let V := (1 / (2 * Real.pi) : ℝ) • mellinVerticalSegment x (negativeLFunctionLogDerivative χ) c H
  have hV : ‖V‖ ≤ (1 / (2 * Real.pi)) *
      (Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M + 2 * (c - a) * x ^ c * M / H ^ 2) := by
    dsimp only [V]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left hrect (by positivity)
  have hsum := norm_add_le (S - V) V
  rw [sub_add_cancel] at hsum
  change ‖S - V‖ ≤ _ at htail
  change ‖S‖ ≤ _
  unfold smoothedMangoldtContourBudget
  linarith

/-- The derivative and norm hypotheses of the contour theorem follow from
the actual nonvanishing rectangle and the checked local expansions. -/
theorem norm_weighted_primitive_mangoldt_sum_le_of_zero_free_rectangle
    {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (x c H δ : ℝ) (hx : 1 ≤ x) (hc : 1 < c) (hcu : c ≤ 2)
    (hH : 0 < H) (hδ : 0 < δ) (hδu : δ ≤ 1 / 16)
    (hfree : ∀ u : ℂ, 1 - 2 * δ ≤ u.re → |u.im| ≤ H + 2 →
      DirichletCharacter.LFunction χ u ≠ 0) :
    ‖weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x‖ ≤
      smoothedMangoldtContourBudget x (1 - δ) c H (primitiveStripLogDerivativeBudget q H δ) := by
  have hnonzero (s : ℂ) (hs : s ∈ Icc (1 - δ) c ×ℂ Icc (-H) H) :
      DirichletCharacter.LFunction χ s ≠ 0 :=
    hfree s (by linarith [hs.1.1]) (by have hh := abs_le.mpr hs.2; linarith)
  have hf := DirichletCharacter.differentiable_LFunction (primitive_character_ne_one hq χ hχ)
  have hd : DifferentiableOn ℂ (negativeLFunctionLogDerivative χ)
      (Icc (1 - δ) c ×ℂ Icc (-H) H) :=
    (hf.deriv.neg.differentiableOn).div hf.differentiableOn hnonzero
  have hbound (s : ℂ) (hs : s ∈ Icc (1 - δ) c ×ℂ Icc (-H) H) :
      ‖negativeLFunctionLogDerivative χ s‖ ≤ primitiveStripLogDerivativeBudget q H δ := by
    rw [negativeLFunctionLogDerivative, neg_div, norm_neg]
    exact norm_logDeriv_LFunction_le_of_zero_free_rectangle hq χ hχ H δ hδ hδu hfree s
      hs.1.1 (hs.1.2.trans hcu) (abs_le.mpr hs.2)
  have hM : 0 ≤ primitiveStripLogDerivativeBudget q H δ :=
    (norm_nonneg (negativeLFunctionLogDerivative χ 1)).trans (hbound 1 (by
      change (1 : ℂ).re ∈ Icc (1 - δ) c ∧ (1 : ℂ).im ∈ Icc (-H) H
      norm_num only [one_re, one_im, mem_Icc]
      constructor <;> constructor <;> linarith))
  exact norm_weighted_mangoldt_sum_le_contour_budget χ x (1 - δ) c H
    (primitiveStripLogDerivativeBudget q H δ) hx (by linarith) (by linarith) hc hH hM hd hbound

/-- A uniform contour estimate with all zero-free and value hypotheses
discharged. The same positive constant works for every conductor and height. -/
theorem exists_uniform_smoothed_primitive_mangoldt_contour_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ (q : ℕ) [NeZero q], 1 < q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ∀ (x c H : ℝ), 1 ≤ x → 1 < c → c ≤ 2 → 0 < H →
          ‖weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x‖ ≤
            smoothedMangoldtContourBudget x
              (1 - primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2) c H
              (primitiveStripLogDerivativeBudget q H
                (primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2)) := by
  obtain ⟨d, hd, hfree⟩ := exists_LFunction_zero_free_rectangle ε hε
  refine ⟨d, hd, ?_⟩
  intro q _ hq χ hχ x c H hx hc hcu hH
  have hwpos := primitiveZeroFreeRectangleWidth_pos ε d hd q (H + 2)
  have hwle := primitiveZeroFreeRectangleWidth_le_one_thirtysecond ε d q (H + 2)
  apply norm_weighted_primitive_mangoldt_sum_le_of_zero_free_rectangle hq χ hχ
    x c H (primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2) hx hc hcu hH
    (by positivity) (by linarith)
  intro u hu hui
  exact hfree q hq χ hχ (H + 2) (by linarith) u (by linarith) hui

end TwinPrime.Analytic
