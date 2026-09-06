import TwinPrime.Analytic.LocalLogDerivativeExpansion
import TwinPrime.Analytic.LFunctionLowerBound
import TwinPrime.Analytic.ZetaLogDerivative
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The local expansion of regularized zeta at every height

The actual zero divisor of the entire function `(s-1)ζ(s)` supplies the
local expansion. Qualitative nonvanishing gives the signs of its reciprocal
zero terms. The resulting one-sided bound for `-ζ'/ζ` retains the principal
pole at arbitrary height, without a quantitative zero-free assumption.
-/

noncomputable section

open Function Metric MeromorphicOn

namespace TwinPrime.Analytic

def localZetaZeroSum (c s : ℂ) : ℂ :=
  ∑ᶠ ρ, (divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)

def zetaLogBudget (t : ℝ) : ℝ :=
  (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
    (1 + Real.log 16 + 2 * Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2))

theorem zetaLogBudget_nonneg (t : ℝ) : 0 ≤ zetaLogBudget t := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hH : 0 ≤ Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) :=
    Real.log_nonneg (by have := norm_nonneg ((2 : ℂ) + Complex.I * t); linarith)
  unfold zetaLogBudget
  positivity

/-- The explicit budget grows only logarithmically with the height. -/
theorem zetaLogBudget_le_log_abs (t : ℝ) :
    zetaLogBudget t ≤
      (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (|t| + 4)) := by
  have hn : ‖(2 : ℂ) + Complex.I * t‖ ≤ |t| + 2 := by
    have h := norm_add_le (2 : ℂ) (Complex.I * t)
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hl : Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) ≤ Real.log (|t| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  unfold zetaLogBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem regularizedRiemannZeta_ne_zero_of_one_le_re (s : ℂ) (hs : 1 ≤ s.re) :
    regularizedRiemannZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · rw [regularizedRiemannZeta_apply_of_ne_one s hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs)

theorem regularizedRiemannZeta_zero_re_lt_one (ρ : ℂ)
    (hρ : regularizedRiemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact regularizedRiemannZeta_ne_zero_of_one_le_re ρ (not_lt.mp h) hρ

theorem one_quarter_le_norm_regularizedRiemannZeta_center (c : ℂ) (hc : c.re = 2) :
    1 / 4 ≤ ‖regularizedRiemannZeta c‖ := by
  have hc1 : c ≠ 1 := by intro h; simp [h] at hc
  have hζ : 1 / 4 ≤ ‖riemannZeta c‖ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      one_quarter_le_norm_LFunction (1 : DirichletCharacter ℂ 1) c (by rw [hc])
  have hsub : 1 ≤ ‖c - 1‖ := by
    have h := Complex.re_le_norm (c - 1)
    simpa only [Complex.sub_re, Complex.one_re, hc, show (2 : ℝ) - 1 = 1 by norm_num] using h
  rw [regularizedRiemannZeta_apply_of_ne_one c hc1, norm_mul]
  calc
    _ ≤ ‖riemannZeta c‖ := hζ
    _ = 1 * ‖riemannZeta c‖ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsub (norm_nonneg _)

theorem regularizedZetaGrowthBudget_half_le (c : ℂ) :
    regularizedZetaGrowthBudget (1 / 2) (‖c‖ + 3 / 2) ≤ 4 * (‖c‖ + 2) ^ 2 := by
  unfold regularizedZetaGrowthBudget
  have hn := norm_nonneg c
  nlinarith [sq_nonneg ‖c‖]

theorem norm_logDeriv_regularizedZeta_sub_zero_sum_le (c : ℂ) (hc : c.re = 2)
    (z : ℂ) (hz : z ∈ closedBall c 1) (hZz : regularizedRiemannZeta z ≠ 0) :
    ‖logDeriv regularizedRiemannZeta z - localZetaZeroSum c z‖ ≤
      (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (‖c‖ + 2)) := by
  let M : ℝ := 4 * (‖c‖ + 2) ^ 2
  have hn := norm_nonneg c
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg ‖c‖]
  have hcenter := one_quarter_le_norm_regularizedRiemannZeta_center c hc
  have hcenter0 : 0 < ‖regularizedRiemannZeta c‖ := by linarith
  have hf : AnalyticOnNhd ℂ regularizedRiemannZeta (closedBall c (3 / 2)) :=
    fun w _ => differentiable_regularizedRiemannZeta.analyticAt w
  have hbound : ∀ w ∈ sphere c (3 / 2), ‖regularizedRiemannZeta w‖ ≤ M := by
    intro w hw
    have ht := norm_regularizedRiemannZeta_le_on_closedBall c (3 / 2)
      (by rw [hc]; norm_num) w (sphere_subset_closedBall hw)
    have ht' : ‖regularizedRiemannZeta w‖ ≤
        regularizedZetaGrowthBudget (1 / 2) (‖c‖ + 3 / 2) := by
      simpa only [hc, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using ht
    exact ht'.trans (regularizedZetaGrowthBudget_half_le c)
  have he := norm_logDeriv_sub_zero_sum_le hf (norm_pos_iff.mp hcenter0) hM hbound z hz hZz
  apply he.trans
  have hratio : M / ‖regularizedRiemannZeta c‖ ≤ 16 * (‖c‖ + 2) ^ 2 := by
    calc
      _ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hcenter
      _ = _ := by dsimp [M]; ring
  have hH : 0 < ‖c‖ + 2 := by positivity
  have hlog : Real.log (M / ‖regularizedRiemannZeta c‖) ≤
      Real.log 16 + 2 * Real.log (‖c‖ + 2) := by
    calc
      _ ≤ Real.log (16 * (‖c‖ + 2) ^ 2) :=
        Real.log_le_log (div_pos (by linarith) hcenter0) hratio
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hH.ne'), Real.log_pow]; norm_num
  apply mul_le_mul_of_nonneg_left (by linarith)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  positivity

theorem regularizedZeta_divisor_re_lt_one (K : Set ℂ) (ρ : ℂ)
    (hρ : divisor regularizedRiemannZeta K ρ ≠ 0) : ρ.re < 1 := by
  have ha := differentiable_regularizedRiemannZeta
  have hK : ρ ∈ K := (divisor regularizedRiemannZeta K).supportWithinDomain hρ
  by_contra hre
  have hn := regularizedRiemannZeta_ne_zero_of_one_le_re ρ (not_lt.mp hre)
  have ho := (ha.analyticAt ρ).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
  rw [divisor_apply (fun z _ => (ha.analyticAt z).meromorphicAt) hK, ho] at hρ
  simp at hρ

theorem regularizedZeta_divisor_term_re_nonneg (K : Set ℂ) (s ρ : ℂ) (hs : 1 < s.re) :
    0 ≤ ((divisor regularizedRiemannZeta K ρ : ℂ) / (s - ρ)).re := by
  by_cases hρ : divisor regularizedRiemannZeta K ρ = 0
  · simp [hρ]
  have hre := regularizedZeta_divisor_re_lt_one K ρ hρ
  have ha : AnalyticOnNhd ℂ regularizedRiemannZeta K :=
    fun z _ => differentiable_regularizedRiemannZeta.analyticAt z
  have hD : (0 : ℝ) ≤ divisor regularizedRiemannZeta K ρ := by
    exact_mod_cast ha.divisor_nonneg ρ
  simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im, Complex.sub_re,
    zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg hD (by linarith)) (Complex.normSq_nonneg _)

theorem localZetaZeroTerm_hasFiniteSupport (c s : ℂ) :
    (fun ρ => (divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) /
      (s - ρ)).HasFiniteSupport := by
  apply ((divisor regularizedRiemannZeta (closedBall c (5 / 4))).finiteSupport
    (isCompact_closedBall c (5 / 4))).subset
  intro ρ hρ
  change divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ ≠ 0
  intro hD
  exact hρ (by simp [hD])

theorem localZetaZeroSum_re_nonneg (c s : ℂ) (hs : 1 < s.re) :
    0 ≤ (localZetaZeroSum c s).re := by
  have he : (localZetaZeroSum c s).re =
      ∑ᶠ ρ, ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re :=
    Complex.reAddGroupHom.map_finsum (localZetaZeroTerm_hasFiniteSupport c s)
  rw [he]
  exact finsum_nonneg (fun ρ => regularizedZeta_divisor_term_re_nonneg _ s ρ hs)

/-- The pole regularization has only the actual zero sum and a controlled
analytic remainder; there is no pole term in this inequality. -/
theorem neg_logDerivative_regularizedZeta_re_le_budget_sub_zeroSum
    (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv regularizedRiemannZeta ((σ : ℂ) + Complex.I * t) /
      regularizedRiemannZeta ((σ : ℂ) + Complex.I * t)).re ≤
        zetaLogBudget t - (localZetaZeroSum ((2 : ℂ) + Complex.I * t)
          ((σ : ℂ) + Complex.I * t)).re := by
  let c : ℂ := (2 : ℂ) + Complex.I * t
  let z : ℂ := (σ : ℂ) + Complex.I * t
  have hc : c.re = 2 := by simp [c]
  have hzr : 1 < z.re := by simpa [z] using hσ
  have hz : z ∈ closedBall c 1 := by
    have heq : z - c = ((σ - 2 : ℝ) : ℂ) := by dsimp [z, c]; push_cast; ring
    rw [mem_closedBall_iff_norm, heq, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb := norm_logDeriv_regularizedZeta_sub_zero_sum_le c hc z hz
    (regularizedRiemannZeta_ne_zero_of_one_le_re z hzr.le)
  change ‖logDeriv regularizedRiemannZeta z - localZetaZeroSum c z‖ ≤ zetaLogBudget t at hb
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (logDeriv regularizedRiemannZeta z - localZetaZeroSum c z))).1
  simp only [Complex.sub_re] at hr
  change (-deriv regularizedRiemannZeta z / regularizedRiemannZeta z).re ≤
    zetaLogBudget t - (localZetaZeroSum c z).re
  rw [neg_div, Complex.neg_re]
  change -(logDeriv regularizedRiemannZeta z).re ≤ _
  linarith

theorem neg_logDerivative_regularizedZeta_re_le_budget
    (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv regularizedRiemannZeta ((σ : ℂ) + Complex.I * t) /
      regularizedRiemannZeta ((σ : ℂ) + Complex.I * t)).re ≤ zetaLogBudget t := by
  apply (neg_logDerivative_regularizedZeta_re_le_budget_sub_zeroSum σ t hσ hσu).trans
  apply sub_le_self
  exact localZetaZeroSum_re_nonneg _ _ (by simpa using hσ)

/-- An all-height upper bound with the principal pole retained exactly. -/
theorem neg_logDerivative_zeta_re_le_pole_add_budget
    (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv riemannZeta ((σ : ℂ) + Complex.I * t) /
      riemannZeta ((σ : ℂ) + Complex.I * t)).re ≤
        (1 / ((σ : ℂ) - 1 + Complex.I * t)).re + zetaLogBudget t := by
  let z : ℂ := (σ : ℂ) + Complex.I * t
  have hzr : 1 < z.re := by simpa [z] using hσ
  have hz1 : z ≠ 1 := by intro h; simp [h] at hzr
  have heq := neg_zeta_logDerivative_eq_pole_sub_regularized z hz1
    (regularizedRiemannZeta_ne_zero_of_one_le_re z hzr.le)
  change (-deriv riemannZeta z / riemannZeta z).re ≤ _
  rw [heq, Complex.sub_re]
  have hb := neg_logDerivative_regularizedZeta_re_le_budget σ t hσ hσu
  change (-deriv regularizedRiemannZeta z / regularizedRiemannZeta z).re ≤ zetaLogBudget t at hb
  rw [neg_div, Complex.neg_re] at hb
  have hshift : z - 1 = (σ : ℂ) - 1 + Complex.I * t := by dsimp [z]; ring
  rw [hshift]
  linarith

end TwinPrime.Analytic
