import TwinPrime.Analytic.LFunctionZeroValue
import TwinPrime.Analytic.LFunctionNearOneGrowth
import TwinPrime.Analytic.ZeroFreeLogarithms

/-!
# Logarithmic-square zero-to-value bound

The actual conductor truncation and real-segment estimate give a zero-distance
bound in terms of the actual value at one. A uniform lower bound for that value
is the separate Siegel input proved in `SiegelValue`.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem primitiveLogZeroFreeWidth_le_one_div_log {q : ℕ}
    (hq : 1 < q) (t : ℝ) :
    primitiveLogZeroFreeWidth q t ≤ 1 / Real.log q := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hH : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_ge
  unfold primitiveLogZeroFreeWidth
  apply one_div_le_one_div_of_le hlog
  nlinarith [mul_nonneg (by linarith : 0 ≤ zeroFreeLogConstant)
    (by linarith : 0 ≤ 1 + Real.log (q : ℝ) + Real.log (|t| + 4))]

/-- The actual value at one is bounded by the distance to any nearby real zero,
with only a logarithmic-square loss. -/
theorem norm_LFunction_one_le_log_sq_gap {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β : ℝ) (hβ : 1 - 1 / Real.log q ≤ β)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (10 * Real.exp 2 * (Real.log q) ^ 2) * (1 - β) := by
  have hq1 : 1 < q := by omega
  have hβ1 : β ≤ 1 := by
    have h := primitiveLFunction_zero_re_lt_one hq1 χ hχ (β : ℂ) hzero
    simpa only [Complex.ofReal_re] using h.le
  apply norm_LFunction_one_le_gap_of_deriv_bound χ (primitive_character_ne_one hq1 χ hχ)
    β _ hβ1 hzero
  intro u hu
  exact norm_deriv_LFunction_near_one_le hq χ hχ u (hβ.trans hu.1) hu.2

theorem real_zero_gap_ge_LFunction_one_div_log_sq {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β : ℝ) (hβ : 1 - 1 / Real.log q ≤ β)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ /
      (10 * Real.exp 2 * (Real.log q) ^ 2) ≤ 1 - β := by
  have hlog : 0 < Real.log (q : ℝ) := by
    linarith [one_le_log_of_256_le q hq]
  apply (div_le_iff₀ (by positivity : 0 < 10 * Real.exp 2 * (Real.log (q : ℝ)) ^ 2)).mpr
  simpa only [mul_comm] using norm_LFunction_one_le_log_sq_gap hq χ hχ β hβ hzero

/-- The possible zero in the checked logarithmic region satisfies the actual
value-dependent gap bound. This theorem does not assert a Siegel lower bound. -/
theorem LFunction_zero_in_log_region_gap {q : ℕ} [NeZero q]
    (hq : 256 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β t : ℝ) (hβ : 1 - primitiveLogZeroFreeWidth q t ≤ β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    χ ^ 2 = 1 ∧ t = 0 ∧
      ‖DirichletCharacter.LFunction χ 1‖ /
        (10 * Real.exp 2 * (Real.log q) ^ 2) ≤ 1 - β := by
  have hq1 : 1 < q := by omega
  obtain ⟨hχ2, ht, _⟩ := LFunction_zero_in_log_region_real_simple hq1 χ hχ β t hβ hzero
  refine ⟨hχ2, ht, real_zero_gap_ge_LFunction_one_div_log_sq hq χ hχ β ?_ ?_⟩
  · have hw := primitiveLogZeroFreeWidth_le_one_div_log hq1 t
    linarith
  · simpa only [ht, Complex.ofReal_zero, mul_zero, add_zero] using hzero

end TwinPrime.Analytic
