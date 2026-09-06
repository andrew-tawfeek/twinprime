import TwinPrime.Analytic.ContourBudgetAbsorption
import TwinPrime.Analytic.PrincipalStripParameters

/-!
# Uniform centered smoothed Siegel--Walfisz

The actual primitive-character contours and the regularized principal contour
share an eventual threshold. All value, nonvanishing, and contour hypotheses
are discharged. The remaining weight is `1 - n / x`.
-/

noncomputable section

open Filter Classical

namespace TwinPrime.Analytic

def centeredWeightedCharacterSum {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x -
    if χ = 1 then (x : ℂ) / 2 else 0

theorem primitiveStripLogDerivativeBudget_nonneg (q : ℕ) (H δ : ℝ)
    (hq : 1 ≤ q) (hH : 0 ≤ H) (hδ : 0 ≤ δ) :
    0 ≤ primitiveStripLogDerivativeBudget q H δ := by
  have hqlog := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
  have hHlog := Real.log_nonneg (show 1 ≤ H + 4 by linarith)
  have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
  have h5 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
  have h65 := Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)
  unfold primitiveStripLogDerivativeBudget
  positivity

theorem zetaStripLogDerivativeBudget_nonneg (H δ : ℝ) (hH : 0 ≤ H) (hδ : 0 ≤ δ) :
    0 ≤ zetaStripLogDerivativeBudget H δ := by
  have hHlog := Real.log_nonneg (show 1 ≤ H + 4 by linarith)
  have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
  have h5 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
  have h65 := Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)
  unfold zetaStripLogDerivativeBudget
  positivity

theorem eventually_log_rpow_le_self (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ A ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop A (s := 1) (by norm_num)).eventuallyLE
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hb hx
  simpa only [Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) A),
    abs_of_nonneg (by linarith : 0 ≤ x)] using hb

/-- A single constant and threshold work for every primitive character of
conductor at most a fixed logarithmic power, including conductor one. -/
theorem smoothed_siegel_walfisz (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ‖centeredWeightedCharacterSum x χ‖ ≤ C * x / (Real.log x) ^ A := by
  let K := A + 2
  have hK : 0 < K := by dsimp [K]; linarith
  let ε := 1 / (2 * B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨d, hd, hprimitive⟩ := exists_uniform_smoothed_primitive_mangoldt_contour_bound ε hε
  let k := siegelWalfiszStripWidthConstant B K d
  let C := 2 * siegelWalfiszStripBudgetConstant B K d
  let E := contourAbsorptionConstant C
  have hk : 0 < k := siegelWalfiszStripWidthConstant_pos B K d hB hK hd
  have hCbase := siegelWalfiszStripBudgetConstant_pos B K d hB hK hd
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 < E := contourAbsorptionConstant_pos C hC
  refine ⟨E + 1, by positivity, ?_⟩
  filter_upwards [eventually_smoothedPrincipalContourBudget_le A k C hA hk hC,
    eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (8 : ℝ)),
    eventually_log_rpow_le_self A] with x habs hx hlog hpow
  intro q hq hqL χ hχ
  letI : NeZero q := ⟨by omega⟩
  let L := Real.log x
  let H := L ^ K
  let c := 1 + 1 / L
  let δ := primitiveZeroFreeRectangleWidth ε d q (H + 2) / 2
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := by linarith
  have hH : 0 < H := Real.rpow_pos_of_pos hL0 K
  have hc : 1 < c := by
    have hi : 0 < 1 / L := by positivity
    dsimp [c]
    linarith
  have hcu : c ≤ 2 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hL
    dsimp [c]
    norm_num only [div_one] at hi
    linarith
  have hδ : 0 < δ := by
    have hw := primitiveZeroFreeRectangleWidth_pos ε d hd q (H + 2)
    dsimp [δ]
    positivity
  have hδu : δ ≤ 1 / 16 := by
    have hw := primitiveZeroFreeRectangleWidth_le_one_thirtysecond ε d q (H + 2)
    dsimp [δ]
    linarith
  have hwidth : k * L ^ (-(1 / 2 : ℝ)) ≤ δ :=
    siegelWalfiszStripWidthConstant_mul_rpow_le B K d L hB hK hd hL q hq hqL
  have hunit : 1 ≤ x / L ^ A := (le_div_iff₀ (Real.rpow_pos_of_pos hL0 A)).mpr (by simpa using hpow)
  have hextra : E * x / L ^ A ≤ (E + 1) * x / L ^ A := by gcongr; linarith
  by_cases hqone : q = 1
  · subst q
    have hχone := DirichletCharacter.level_one χ
    have hb := (principal_common_strip_width_and_budget B K d L hB hK hd hL).2
    have hM := zetaStripLogDerivativeBudget_nonneg H δ hH.le hδ.le
    have ha := habs δ (zetaStripLogDerivativeBudget H δ) hδ hδu hwidth hM hb
    have hs := norm_weighted_vonMangoldt_sub_half_le_at_common_width ε d x c H hd hx.le hc hcu hH
    have heq : centeredWeightedCharacterSum x χ =
        weightedPartialSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) x -
          ((x / 2 : ℝ) : ℂ) := by
      rw [hχone]
      simp only [centeredWeightedCharacterSum]
      rw [← weighted_vonMangoldt_sum_eq_modOne x]
      norm_cast
    rw [heq]
    change ‖_‖ ≤ smoothedPrincipalContourBudget x (1 - δ) c H
      (zetaStripLogDerivativeBudget H δ) + 1 at hs
    change smoothedPrincipalContourBudget x (1 - δ) c H
      (zetaStripLogDerivativeBudget H δ) ≤ E * x / L ^ A at ha
    have hend : E * x / L ^ A + 1 ≤ (E + 1) * x / L ^ A := by
      calc
        _ ≤ E * x / L ^ A + x / L ^ A := _root_.add_le_add le_rfl hunit
        _ = _ := by ring
    exact hs.trans ((_root_.add_le_add ha le_rfl).trans hend)
  · have hqgt : 1 < q := by omega
    have hχne := primitive_character_ne_one hqgt χ hχ
    have hMb : primitiveStripLogDerivativeBudget q H δ ≤ C * L := by
      have hb := siegelWalfiszStripBudgetConstant_bound B K d L hB hK hd hL q hq hqL
      change primitiveStripLogDerivativeBudget q H δ ≤ _ at hb
      apply hb.trans
      dsimp [C]
      nlinarith
    have hM := primitiveStripLogDerivativeBudget_nonneg q H δ hq hH.le hδ.le
    have ha := habs δ (primitiveStripLogDerivativeBudget q H δ) hδ hδu hwidth hM hMb
    have hs := hprimitive q hqgt χ hχ x c H hx.le hc hcu hH
    simp only [centeredWeightedCharacterSum, if_neg hχne, sub_zero]
    apply hs.trans
    apply (smoothedMangoldtContourBudget_le_principal x (1 - δ) c H
      (primitiveStripLogDerivativeBudget q H δ) hx0.le hc hH).trans
    exact ha.trans hextra

end TwinPrime.Analytic
