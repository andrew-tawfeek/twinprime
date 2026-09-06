import TwinPrime.Analytic.ZetaLocalExpansion
import TwinPrime.Analytic.LFunctionNonquadraticZeroFree

/-!

# An explicit zero-free region for regularized zeta

The entire regularization retains value one at the principal pole. Its
actual zeros provide the selected reciprocal term in three-four-one.
An explicit disk handles small heights; the principal pole contributions
are controlled directly at larger heights.
-/

noncomputable section

open Function Metric MeromorphicOn

namespace TwinPrime.Analytic

theorem meromorphicOrderAt_regularizedZeta_ne_top (ρ : ℂ) :
    meromorphicOrderAt regularizedRiemannZeta ρ ≠ ⊤ := by
  have hF : AnalyticOnNhd ℂ regularizedRiemannZeta Set.univ :=
    fun z _ => differentiable_regularizedRiemannZeta.analyticAt z
  apply hF.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (1 : ℂ)) (Set.mem_univ ρ)
  have hn := (differentiable_regularizedRiemannZeta.analyticAt (1 : ℂ)).meromorphicNFAt
  rw [hn.meromorphicOrderAt_eq_zero_iff.mpr (by simp : regularizedRiemannZeta 1 ≠ 0)]
  simp

theorem one_le_regularizedZeta_divisor_of_zero (K : Set ℂ) (ρ : ℂ)
    (hK : ρ ∈ K) (hρ : regularizedRiemannZeta ρ = 0) :
    1 ≤ divisor regularizedRiemannZeta K ρ := by
  have hF : AnalyticOnNhd ℂ regularizedRiemannZeta K :=
    fun z _ => differentiable_regularizedRiemannZeta.analyticAt z
  have hn : MeromorphicNFOn regularizedRiemannZeta K := fun z hz => (hF z hz).meromorphicNFAt
  have heq := hn.zero_set_eq_divisor_support (fun z => meromorphicOrderAt_regularizedZeta_ne_top z)
  have hsupport : ρ ∈ (divisor regularizedRiemannZeta K).support := heq.subset ⟨hK, hρ⟩
  have hnonneg : 0 ≤ divisor regularizedRiemannZeta K ρ := hF.divisor_nonneg ρ
  change divisor regularizedRiemannZeta K ρ ≠ 0 at hsupport
  omega

theorem localZetaZeroSum_re (c s : ℂ) :
    (localZetaZeroSum c s).re =
      ∑ᶠ ρ, ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re :=
  Complex.reAddGroupHom.map_finsum (localZetaZeroTerm_hasFiniteSupport c s)

theorem regularizedZeta_divisor_term_re_le_zeroSum (c s ρ : ℂ) (hs : 1 < s.re) :
    ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re ≤
      (localZetaZeroSum c s).re := by
  rw [localZetaZeroSum_re]
  apply single_le_finsum ρ
  · apply ((divisor regularizedRiemannZeta (closedBall c (5 / 4))).finiteSupport
      (isCompact_closedBall c (5 / 4))).subset
    intro u hu
    change divisor regularizedRiemannZeta (closedBall c (5 / 4)) u ≠ 0
    intro hD
    exact hu (by simp [hD])
  · exact fun u => regularizedZeta_divisor_term_re_nonneg _ s u hs

/-- A selected actual zero of the entire regularization contributes with
positive integer multiplicity. The pole at one is never counted as a zero. -/
theorem one_div_sub_le_localZetaZeroSum_re_of_zero (β t σ : ℝ)
    (hβ : 3 / 4 ≤ β) (hσ : 1 < σ)
    (hzero : regularizedRiemannZeta ((β : ℂ) + Complex.I * t) = 0) :
    1 / (σ - β) ≤
      (localZetaZeroSum ((2 : ℂ) + Complex.I * t) ((σ : ℂ) + Complex.I * t)).re := by
  let ρ : ℂ := (β : ℂ) + Complex.I * t
  let c : ℂ := (2 : ℂ) + Complex.I * t
  let s : ℂ := (σ : ℂ) + Complex.I * t
  have hβ1 : β < 1 := by simpa [ρ] using regularizedRiemannZeta_zero_re_lt_one ρ hzero
  have hdiff : ρ - c = ((β - 2 : ℝ) : ℂ) := by dsimp [ρ, c]; push_cast; ring
  have hmem : ρ ∈ closedBall c (5 / 4) := by
    rw [mem_closedBall_iff_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmult := one_le_regularizedZeta_divisor_of_zero (closedBall c (5 / 4)) ρ hmem hzero
  have hmultR : (1 : ℝ) ≤ divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ := by
    exact_mod_cast hmult
  have heval : s - ρ = ((σ - β : ℝ) : ℂ) := by dsimp [s, ρ]; push_cast; ring
  have hs : 1 < s.re := by simpa [s] using hσ
  calc
    _ ≤ (divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℝ) / (σ - β) :=
      div_le_div_of_nonneg_right hmultR (by linarith)
    _ = ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re := by
      rw [heval, Complex.div_ofReal_re, Complex.intCast_re]
    _ ≤ _ := regularizedZeta_divisor_term_re_le_zeroSum c s ρ hs

theorem neg_logDerivative_zeta_re_le_pole_add_budget_sub_one_div_of_zero
    (β t σ : ℝ) (hβ : 3 / 4 ≤ β) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8)
    (hzero : regularizedRiemannZeta ((β : ℂ) + Complex.I * t) = 0) :
    (-deriv riemannZeta ((σ : ℂ) + Complex.I * t) /
      riemannZeta ((σ : ℂ) + Complex.I * t)).re ≤
      (1 / ((σ : ℂ) - 1 + Complex.I * t)).re + zetaLogBudget t - 1 / (σ - β) := by
  let z : ℂ := (σ : ℂ) + Complex.I * t
  have hzr : 1 < z.re := by simpa [z] using hσ
  have hz1 : z ≠ 1 := by intro h; simp [h] at hzr
  have heq := neg_zeta_logDerivative_eq_pole_sub_regularized z hz1
    (regularizedRiemannZeta_ne_zero_of_one_le_re z hzr.le)
  have hb := neg_logDerivative_regularizedZeta_re_le_budget_sub_zeroSum σ t hσ hσu
  have hs := one_div_sub_le_localZetaZeroSum_re_of_zero β t σ hβ hσ hzero
  change (-deriv riemannZeta z / riemannZeta z).re ≤ _
  rw [heq, Complex.sub_re]
  change (-deriv regularizedRiemannZeta z / regularizedRiemannZeta z).re ≤ _ at hb
  rw [neg_div, Complex.neg_re] at hb
  have hshift : z - 1 = (σ : ℂ) - 1 + Complex.I * t := by dsimp [z]; ring
  rw [hshift]
  linarith

theorem principal_pole_re_at_height (a t : ℝ) :
    (1 / ((a : ℂ) + Complex.I * t)).re = a / (a ^ 2 + t ^ 2) := by
  simp only [Complex.div_re, Complex.normSq_apply, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem principal_pole_re_le_one_seventeenth (a t : ℝ) (ha : 0 < a) (ht : 4 * a ≤ |t|) :
    (1 / ((a : ℂ) + Complex.I * t)).re ≤ 1 / (17 * a) := by
  rw [principal_pole_re_at_height]
  have hsq : 16 * a ^ 2 ≤ t ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ 4 * a) ht
    nlinarith [sq_abs t]
  apply (div_le_div_iff₀ (by positivity : 0 < a ^ 2 + t ^ 2)
    (by positivity : 0 < 17 * a)).mpr
  nlinarith

theorem four_three_five_seventeenths_pole_contradiction {E δ : ℝ} (hE : 0 < E)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (80 * E)) :
    ¬ 4 / (1 / (4 * E) + δ) ≤
      3 / (1 / (4 * E)) + 5 / (17 * (1 / (4 * E))) + E := by
  have ha : 0 < 1 / (4 * E) := by positivity
  have hden : 0 < 1 / (4 * E) + δ := by linarith
  have hsum : 1 / (4 * E) + 1 / (80 * E) = 21 / (80 * E) := by field_simp; ring
  have hbound : 1 / (4 * E) + δ ≤ 21 / (80 * E) := by linarith
  have hlo : 320 * E / 21 ≤ 4 / (1 / (4 * E) + δ) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 320 * E / 21)
    have heq : (320 * E / 21) * (21 / (80 * E)) = 4 := by field_simp; ring
    linarith
  have hr : 3 / (1 / (4 * E)) + 5 / (17 * (1 / (4 * E))) + E = 241 * E / 17 := by
    field_simp
    ring
  rw [hr]
  linarith

def zetaZeroFreeBudget (t : ℝ) : ℝ :=
  120 + 4 * zetaLogBudget t + zetaLogBudget (2 * t)

theorem zetaZeroFreeBudget_ge (t : ℝ) : 120 ≤ zetaZeroFreeBudget t := by
  have hZ := zetaLogBudget_nonneg t
  have hZ2 := zetaLogBudget_nonneg (2 * t)
  unfold zetaZeroFreeBudget
  linarith

theorem four_div_sub_le_of_regularizedZeta_zero (β t σ : ℝ)
    (hβ : 3 / 4 ≤ β) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8)
    (hzero : regularizedRiemannZeta ((β : ℂ) + Complex.I * t) = 0) :
    4 / (σ - β) ≤ 3 / (σ - 1) +
      4 * (1 / ((σ : ℂ) - 1 + Complex.I * t)).re +
      (1 / ((σ : ℂ) - 1 + Complex.I * (2 * t : ℝ))).re + zetaZeroFreeBudget t := by
  have hp := three_four_one_LFunction_logDerivative_nonneg
    (1 : DirichletCharacter ℂ 1) hσ t
  simp only [one_pow, DirichletCharacter.LFunction_modOne_eq] at hp
  have hz := neg_zeta_logDerivative_real_le_pole_add_forty σ hσ hσu
  have hfirst := neg_logDerivative_zeta_re_le_pole_add_budget_sub_one_div_of_zero
    β t σ hβ hσ hσu hzero
  have hsecond := neg_logDerivative_zeta_re_le_pole_add_budget σ (2 * t) hσ hσu
  rw [show 4 / (σ - β) = 4 * (1 / (σ - β)) by ring,
    show 3 / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  unfold zetaZeroFreeBudget
  linarith

/-- An explicit all-height zero-free region for the actual entire pole
regularization. In particular its nonzero value at one is preserved. -/
theorem regularizedRiemannZeta_ne_zero_of_re_ge_one_sub_budget (β t : ℝ)
    (hβ : 1 - 1 / (80 * zetaZeroFreeBudget t) ≤ β) :
    regularizedRiemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 := by
  intro hzero
  let E := zetaZeroFreeBudget t
  let a : ℝ := 1 / (4 * E)
  have hE : 120 ≤ E := zetaZeroFreeBudget_ge t
  have hE0 : 0 < E := by linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hau : a ≤ 1 / 480 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 4 * E)).mpr
    linarith
  have heps : 1 / (80 * E) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 80 * E)).mpr
    linarith
  have hβ1 : β < 1 := by
    simpa using regularizedRiemannZeta_zero_re_lt_one ((β : ℂ) + Complex.I * t) hzero
  have hδ : 1 - β ≤ 1 / (80 * E) := by dsimp [E]; linarith
  by_cases ht : |t| ≤ 1 / 8
  · have hβabs : |β - 1| ≤ 1 / 8 := by
      rw [abs_of_nonpos (by linarith : β - 1 ≤ 0)]
      linarith
    have hnorm : ‖(β : ℂ) + Complex.I * t - 1‖ ≤ 1 / 4 := by
      have heq : (β : ℂ) + Complex.I * t - 1 = ((β - 1 : ℝ) : ℂ) + Complex.I * t := by
        push_cast
        ring
      rw [heq]
      have hn := norm_add_le (((β - 1 : ℝ) : ℂ)) (Complex.I * t)
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul] at hn
      linarith
    exact regularizedRiemannZeta_ne_zero_of_norm_sub_one_le _ hnorm hzero
  · have htlarge : 4 * a ≤ |t| := by linarith
    have htlarge2 : 4 * a ≤ |2 * t| := by
      rw [abs_mul]
      norm_num
      linarith [abs_nonneg t]
    have hβlow : 3 / 4 ≤ β := by linarith
    have hσ : 1 < 1 + a := by linarith
    have hσu : 1 + a ≤ 9 / 8 := by linarith
    have hineq := four_div_sub_le_of_regularizedZeta_zero β t (1 + a) hβlow hσ hσu hzero
    have hshift : ((1 + a : ℝ) : ℂ) - 1 = (a : ℂ) := by push_cast; ring
    rw [show 1 + a - β = a + (1 - β) by ring, add_sub_cancel_left, hshift] at hineq
    have hpole := principal_pole_re_le_one_seventeenth a t ha0 htlarge
    have hpole2 := principal_pole_re_le_one_seventeenth a (2 * t) ha0 htlarge2
    have hbad : 4 / (a + (1 - β)) ≤ 3 / a + 5 / (17 * a) + E := by
      change 4 / (a + (1 - β)) ≤ 3 / a +
        4 * (1 / ((a : ℂ) + Complex.I * t)).re +
        (1 / ((a : ℂ) + Complex.I * (2 * t : ℝ))).re + E at hineq
      rw [show 5 / (17 * a) = 5 * (1 / (17 * a)) by ring]
      linarith
    exact four_three_five_seventeenths_pole_contradiction hE0 (by linarith) hδ hbad

/-- Away from the pole, the same region excludes zeros of the actual zeta function. -/
theorem riemannZeta_ne_zero_of_re_ge_one_sub_budget (β t : ℝ)
    (hβ : 1 - 1 / (80 * zetaZeroFreeBudget t) ≤ β)
    (hs1 : (β : ℂ) + Complex.I * t ≠ 1) :
    riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 := by
  have h := regularizedRiemannZeta_ne_zero_of_re_ge_one_sub_budget β t hβ
  rw [regularizedRiemannZeta_apply_of_ne_one _ hs1] at h
  exact (mul_ne_zero_iff.mp h).2

end TwinPrime.Analytic
