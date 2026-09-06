import TwinPrime.Analytic.LogarithmicCorrection
import TwinPrime.Analytic.BilinearCutoffShift

/-!
# Keeping the finite classical main terms in the correlation

The center retains the actual finite Möbius/totient coefficients. Its error
therefore involves only the three progression errors, without replacing those
coefficients by their limits. The same convention cancels the main coefficient
of a right-cutoff change exactly.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The finite mixed, logarithmic, and Type I main terms, with their exact signs. -/
def classicalCorrelationCenter (U V X : ℕ) : ℝ :=
  (X : ℝ) * smoothedTotientSum U +
    oddMoebiusTotientSum U * logarithmicMass U X - (X : ℝ) * totientTypeIMain U V

/-- The discrepancy from the centered bilinear expression is exactly the sum
of the three classical progression remainders. -/
theorem correlation_sub_bilinear_add_classicalCenter_eq (U V X : ℕ)
    (hU : 0 < U) (hV : V ≤ X) :
    W2 X - (bilinearTerm U V X + classicalCorrelationCenter U V X) =
      (mixedCorrelation U X - (X : ℝ) * smoothedTotientSum U) +
      (logarithmicCorrection U X -
        oddMoebiusTotientSum U * logarithmicMass U X) -
      (typeITerm U V X - (X : ℝ) * totientTypeIMain U V) := by
  rw [correlation_decomposition U V X hU hV]
  unfold classicalCorrelationCenter typeICorrection
  ring

/-- A finite bound with all three actual progression budgets displayed. -/
theorem classicalCorrelationCenter_error_le (U V X : ℕ)
    (hU : 0 < U) (hUX : U ≤ X) (hV : V ≤ X) :
    |W2 X - (bilinearTerm U V X + classicalCorrelationCenter U V X)| ≤
      (2 * Real.log (U + 1) *
          ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q +
        (U + 1 : ℝ) * Real.log (U + 1) * evenProgressionBound X) +
      (4 * Real.log (2 * X + 2) *
          ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q +
        (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X) +
      (2 * Real.log (U * V + 1) *
          ∑ q ∈ Icc 1 (U * V), progressionMaxError (2 * X + 2) q +
        (U * V + 1 : ℝ) * Real.log (U * V + 1) * evenProgressionBound X) := by
  rw [correlation_sub_bilinear_add_classicalCenter_eq U V X hU hV]
  exact (abs_sub
    ((mixedCorrelation U X - (X : ℝ) * smoothedTotientSum U) +
      (logarithmicCorrection U X - oddMoebiusTotientSum U * logarithmicMass U X))
    (typeITerm U V X - (X : ℝ) * totientTypeIMain U V)).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (mixedCorrelation_error_le U X)
        (logarithmicCorrection_error_le U X hU hUX))) (typeICorrelation_error_le U V X))

/-- One modulus range suffices when the two positive cutoffs have product at
most `X`. The coefficient `8` retains the three odd error factors `2+4+2`. -/
theorem classicalCorrelationCenter_error_le_product (U V X : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ X) :
    |W2 X - (bilinearTerm U V X + classicalCorrelationCenter U V X)| ≤
      8 * Real.log (2 * X + 2) *
          (∑ q ∈ Icc 1 (U * V), progressionMaxError (2 * X + 2) q) +
      3 * (U * V + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X := by
  have hUUV : U ≤ U * V := Nat.le_mul_of_pos_right U hV
  have hVUV : V ≤ U * V := Nat.le_mul_of_pos_left V hU
  have hUX := hUUV.trans hUV
  have hVX := hVUV.trans hUV
  let L : ℝ := Real.log (2 * X + 2)
  let E : ℝ := ∑ q ∈ Icc 1 (U * V), progressionMaxError (2 * X + 2) q
  let D : ℝ := (U * V + 1 : ℝ) * L * evenProgressionBound X
  have hL : 0 ≤ L := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) X
    linarith)
  have hE : 0 ≤ E := sum_nonneg fun q _ => progressionMaxError_nonneg _ q
  have hsum : (∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q) ≤ E := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      exact mem_Icc.mpr ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2.trans hUUV⟩
    · exact fun q _ _ => progressionMaxError_nonneg _ q
  have hlogU : Real.log (U + 1) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show U + 1 ≤ 2 * X + 2 by omega)
  have hlogUV : Real.log (U * V + 1) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show U * V + 1 ≤ 2 * X + 2 by omega)
  have hcount : (U + 1 : ℝ) ≤ (U * V + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hUUV 1
  have hsum0 : 0 ≤ ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q :=
    sum_nonneg fun q _ => progressionMaxError_nonneg _ q
  have hA : |mixedCorrelation U X - (X : ℝ) * smoothedTotientSum U| ≤ 2 * L * E + D := by
    apply (mixedCorrelation_error_le U X).trans
    apply add_le_add
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hlogU (by norm_num)) hsum hsum0 (by positivity)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul hcount hlogU (Real.log_nonneg (by
          have := Nat.cast_nonneg (α := ℝ) U
          linarith)) (by positivity))
        (evenProgressionBound_nonneg X)
  have hH : |logarithmicCorrection U X -
      oddMoebiusTotientSum U * logarithmicMass U X| ≤ 4 * L * E + D := by
    apply (logarithmicCorrection_error_le U X hU hUX).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hsum (by positivity)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hL)
        (evenProgressionBound_nonneg X)
  have hI : |typeITerm U V X - (X : ℝ) * totientTypeIMain U V| ≤ 2 * L * E + D := by
    apply (typeICorrelation_error_le U V X).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogUV (by norm_num)) hE
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogUV (by positivity))
        (evenProgressionBound_nonneg X)
  rw [correlation_sub_bilinear_add_classicalCenter_eq U V X hU hVX]
  calc
    _ ≤ (2 * L * E + D) + (4 * L * E + D) + (2 * L * E + D) :=
      (abs_sub
        ((mixedCorrelation U X - (X : ℝ) * smoothedTotientSum U) +
          (logarithmicCorrection U X - oddMoebiusTotientSum U * logarithmicMass U X))
        (typeITerm U V X - (X : ℝ) * totientTypeIMain U V)).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add hA hH)) hI)
    _ = _ := by dsimp [L, E, D]; ring

/-- Centering retains the precise Type I remainder under a right-cutoff change. -/
theorem centered_bilinear_cutoff_shift_eq (U V W X : ℕ)
    (hV : V ≤ X) (hW : W ≤ X) :
    (bilinearTerm U V X + classicalCorrelationCenter U V X) -
        (bilinearTerm U W X + classicalCorrelationCenter U W X) =
      (typeITerm U V X - (X : ℝ) * totientTypeIMain U V) -
        (typeITerm U W X - (X : ℝ) * totientTypeIMain U W) := by
  have h := bilinearTerm_sub_eq_typeITerm_sub U V W X hV hW
  unfold classicalCorrelationCenter
  linarith

/-- The exact centered cutoff change inherits the two finite Type I budgets. -/
theorem centered_bilinear_cutoff_shift_error_le (U V W X : ℕ)
    (hV : V ≤ X) (hW : W ≤ X) :
    |(bilinearTerm U V X + classicalCorrelationCenter U V X) -
        (bilinearTerm U W X + classicalCorrelationCenter U W X)| ≤
      (2 * Real.log (U * V + 1) *
        ∑ q ∈ Icc 1 (U * V), progressionMaxError (2 * X + 2) q +
        (U * V + 1 : ℝ) * Real.log (U * V + 1) * evenProgressionBound X) +
      (2 * Real.log (U * W + 1) *
        ∑ q ∈ Icc 1 (U * W), progressionMaxError (2 * X + 2) q +
        (U * W + 1 : ℝ) * Real.log (U * W + 1) * evenProgressionBound X) := by
  rw [centered_bilinear_cutoff_shift_eq U V W X hV hW]
  exact (abs_sub _ _).trans (add_le_add
    (typeICorrelation_error_le U V X) (typeICorrelation_error_le U W X))

end TwinPrime.Analytic
