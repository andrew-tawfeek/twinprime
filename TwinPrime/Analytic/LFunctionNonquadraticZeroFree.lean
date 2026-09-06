import TwinPrime.Analytic.LFunctionInducedBound
import TwinPrime.Analytic.LFunctionLogDerivative
import TwinPrime.Analytic.ZetaLogDerivative
import TwinPrime.Analytic.ZeroFreeArithmetic

/-!
# An explicit zero-free region for nonquadratic primitive characters

The character square is induced to its actual primitive character before
applying the one-sided bound. The principal zeta pole remains in the
three-four-one inequality. The case `χ ^ 2 = 1` is not covered here.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem neg_zeta_logDerivative_real_le_pole_add_forty (σ : ℝ)
    (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 40 := by
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
  have hs : ‖(σ : ℂ) - 1‖ ≤ 1 / 8 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb := norm_neg_zeta_logDerivative_sub_pole_le_forty (σ : ℂ) hs1 hs
  have hr := (Complex.re_le_norm
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - 1 / ((σ : ℂ) - 1))).trans hb
  have hp : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [Complex.sub_re, hp] at hr
  linarith

def nonquadraticZeroFreeBudget (q : ℕ) (t : ℝ) : ℝ :=
  120 + 4 * primitiveLFunctionLogBudget q t + primitiveLFunctionLogBudget q (2 * t) + Real.log q

theorem nonquadraticZeroFreeBudget_ge (q : ℕ) (t : ℝ) :
    120 ≤ nonquadraticZeroFreeBudget q t := by
  have hk := primitiveLFunctionLogBudget_nonneg q t
  have hk2 := primitiveLFunctionLogBudget_nonneg q (2 * t)
  have hq := Real.log_natCast_nonneg q
  unfold nonquadraticZeroFreeBudget
  linarith

/-- The three-four-one inequality with an actual zero and the induced
nonprincipal square gives a scalar inequality with an explicit budget. -/
theorem four_div_sub_le_of_nonquadratic_zero {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ2 : χ ^ 2 ≠ 1)
    (β t σ : ℝ) (hβ : 3 / 4 ≤ β) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    4 / (σ - β) ≤ 3 / (σ - 1) + nonquadraticZeroFreeBudget q t := by
  have hp := three_four_one_LFunction_logDerivative_nonneg χ hσ t
  have hz := neg_zeta_logDerivative_real_le_pole_add_forty σ hσ hσu
  have hfirst := neg_logDerivative_LFunction_re_le_budget_sub_one_div_of_zero
    hq χ hχ β t σ hβ hσ hσu hzero
  have hsecond := neg_logDerivative_LFunction_re_le_budget_add_log
    (χ ^ 2) hχ2 σ (2 * t) hσ hσu
  unfold nonquadraticZeroFreeBudget
  rw [show 4 / (σ - β) = 4 * (1 / (σ - β)) by ring,
    show 3 / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  linarith

/-- A quantitative zero-free region, uniform in conductor and height,
for primitive characters whose square is nonprincipal. -/
theorem LFunction_ne_zero_of_nonquadratic {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ2 : χ ^ 2 ≠ 1)
    (β t : ℝ) (hβ : 1 - 1 / (20 * nonquadraticZeroFreeBudget q t) ≤ β) :
    DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) ≠ 0 := by
  intro hzero
  let E := nonquadraticZeroFreeBudget q t
  have hE : 120 ≤ E := nonquadraticZeroFreeBudget_ge q t
  have hE0 : 0 < E := by linarith
  obtain ⟨ha0, hau, he0, heu⟩ := zero_free_parameters_le hE
  have hβ1 : β < 1 := by
    simpa using primitiveLFunction_zero_re_lt_one hq χ hχ
      ((β : ℂ) + Complex.I * t) hzero
  have hδ : 1 - β ≤ 1 / (20 * E) := by dsimp [E]; linarith
  have hβlow : 3 / 4 ≤ β := by linarith
  have hσ : 1 < 1 + 1 / (4 * E) := by linarith
  have hσu : 1 + 1 / (4 * E) ≤ 9 / 8 := by linarith
  have hineq := four_div_sub_le_of_nonquadratic_zero hq χ hχ hχ2 β t
    (1 + 1 / (4 * E)) hβlow hσ hσu hzero
  have hrewrite : 1 + 1 / (4 * E) - β = 1 / (4 * E) + (1 - β) := by ring
  rw [hrewrite, add_sub_cancel_left] at hineq
  exact four_three_pole_contradiction hE0 (by linarith) hδ hineq

end TwinPrime.Analytic
