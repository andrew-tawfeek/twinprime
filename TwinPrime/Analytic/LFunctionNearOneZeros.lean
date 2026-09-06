import TwinPrime.Analytic.LFunctionNonquadraticZeroFree
import TwinPrime.Analytic.LFunctionConjugateZeros

/-!
# Uniqueness and simplicity of a zero very near one

At a real evaluation point just to the right of one, the actual zero sum
has an upper bound `5 E`. Each zero in the specified rectangle contributes
at least `3 E`, with its actual multiplicity. Thus there is at most one
such zero and its multiplicity is one. For a real character conjugation
then forces the zero to be real. This does not bound its distance from one
by a Siegel-type power of the conductor.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

def nearOneZeroBudget (q : ℕ) : ℝ := 40 + primitiveLFunctionLogBudget q 0

def nearOneEvaluationShift (q : ℕ) : ℝ := 1 / (4 * nearOneZeroBudget q)

def nearOneZeroWidth (q : ℕ) : ℝ := 1 / (16 * nearOneZeroBudget q)

theorem nearOneZeroBudget_ge (q : ℕ) : 40 ≤ nearOneZeroBudget q := by
  have h := primitiveLFunctionLogBudget_nonneg q 0
  unfold nearOneZeroBudget
  linarith

theorem nearOneZeroBudget_pos (q : ℕ) : 0 < nearOneZeroBudget q := by
  have h := nearOneZeroBudget_ge q
  linarith

theorem nearOneEvaluationShift_pos (q : ℕ) : 0 < nearOneEvaluationShift q := by
  unfold nearOneEvaluationShift
  exact one_div_pos.mpr (mul_pos (by norm_num) (nearOneZeroBudget_pos q))

theorem nearOneEvaluationShift_le_one_eighth (q : ℕ) : nearOneEvaluationShift q ≤ 1 / 8 := by
  have h := nearOneZeroBudget_ge q
  unfold nearOneEvaluationShift
  apply (div_le_iff₀ (by linarith : 0 < 4 * nearOneZeroBudget q)).mpr
  linarith

theorem nearOneZeroWidth_eq_shift_div_four (q : ℕ) :
    nearOneZeroWidth q = nearOneEvaluationShift q / 4 := by
  unfold nearOneZeroWidth nearOneEvaluationShift
  ring

theorem nearOneZeroWidth_pos (q : ℕ) : 0 < nearOneZeroWidth q := by
  rw [nearOneZeroWidth_eq_shift_div_four]
  exact div_pos (nearOneEvaluationShift_pos q) (by norm_num)

theorem nearOneZeroWidth_le_one_eighth (q : ℕ) : nearOneZeroWidth q ≤ 1 / 8 := by
  rw [nearOneZeroWidth_eq_shift_div_four]
  have h := nearOneEvaluationShift_le_one_eighth q
  linarith

/-- The reciprocal kernel has a uniform lower bound in the small rectangle. -/
theorem nearOne_reciprocal_kernel_lower {a δ t : ℝ} (ha : 0 < a)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ a / 4) (ht : |t| ≤ a / 4) :
    3 / (4 * a) ≤ (a + δ) / ((a + δ) ^ 2 + t ^ 2) := by
  have had : a * δ ≤ a ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_left hδ ha.le
    nlinarith
  have hd2 : δ ^ 2 ≤ a ^ 2 / 16 := by
    have h := mul_nonneg hδ0 (sub_nonneg.mpr hδ)
    nlinarith
  have ht2 : t ^ 2 ≤ a ^ 2 / 16 := by
    have htl := (abs_le.mp ht).1
    have htu := (abs_le.mp ht).2
    have h := mul_nonneg (by linarith : 0 ≤ a / 4 - t) (by linarith : 0 ≤ a / 4 + t)
    nlinarith
  have hden : 0 < (a + δ) ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg t, sq_pos_of_pos (by linarith : 0 < a + δ)]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * a) hden).mpr
  nlinarith

theorem localLFunctionZeroSum_real_le_pole_add_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (σ : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (localLFunctionZeroSum χ (2 : ℂ) (σ : ℂ)).re ≤
      1 / (σ - 1) + nearOneZeroBudget q := by
  have hn : ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ) /
      DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ 1 / (σ - 1) + 40 := by
    have hb := norm_LFunction_logDerivative_le_zeta χ (s := (σ : ℂ)) (by simpa using hσ)
    exact hb.trans (neg_zeta_logDerivative_real_le_pole_add_forty σ hσ hσu)
  have hr := (Complex.re_le_norm
    (deriv (DirichletCharacter.LFunction χ) (σ : ℂ) /
      DirichletCharacter.LFunction χ (σ : ℂ))).trans hn
  have hs := neg_logDerivative_LFunction_re_le_budget_sub_zeroSum hq χ hχ σ 0 hσ hσu
  simp only [Complex.ofReal_zero, mul_zero, add_zero, neg_div, Complex.neg_re] at hs
  unfold nearOneZeroBudget
  linarith

theorem localLFunctionZeroSum_nearOne_le_five_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (localLFunctionZeroSum χ (2 : ℂ) ((1 + nearOneEvaluationShift q : ℝ) : ℂ)).re ≤
      5 * nearOneZeroBudget q := by
  have ha := nearOneEvaluationShift_pos q
  have hau := nearOneEvaluationShift_le_one_eighth q
  have h := localLFunctionZeroSum_real_le_pole_add_budget hq χ hχ
    (1 + nearOneEvaluationShift q) (by linarith) (by linarith)
  have he : 1 / nearOneEvaluationShift q = 4 * nearOneZeroBudget q := by
    simp [nearOneEvaluationShift, one_div]
  simpa only [add_sub_cancel_left, he, show (4 : ℝ) * nearOneZeroBudget q +
    nearOneZeroBudget q = 5 * nearOneZeroBudget q by ring] using h

theorem nearOne_zero_mem_local_disk {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ)
    (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ρ ∈ closedBall (2 : ℂ) (5 / 4) := by
  have hβ1 := primitiveLFunction_zero_re_lt_one hq χ hχ ρ hzero
  have heps := nearOneZeroWidth_le_one_eighth q
  have hn := Complex.norm_le_abs_re_add_abs_im (ρ - 2)
  norm_num [abs_of_nonpos (by linarith : ρ.re - 2 ≤ 0)] at hn
  rw [mem_closedBall_iff_norm]
  linarith

theorem nearOne_zero_reciprocal_re_ge_three_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ)
    (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    3 * nearOneZeroBudget q ≤
      (1 / (((1 + nearOneEvaluationShift q : ℝ) : ℂ) - ρ)).re := by
  have hβ1 := primitiveLFunction_zero_re_lt_one hq χ hχ ρ hzero
  have hδ : 1 - ρ.re ≤ nearOneEvaluationShift q / 4 := by
    rw [← nearOneZeroWidth_eq_shift_div_four]
    linarith
  have htl : |ρ.im| ≤ nearOneEvaluationShift q / 4 := by
    rwa [← nearOneZeroWidth_eq_shift_div_four]
  have hb := nearOne_reciprocal_kernel_lower (nearOneEvaluationShift_pos q)
    (by linarith : 0 ≤ 1 - ρ.re) hδ htl
  have hrepr : ρ = (ρ.re : ℂ) + Complex.I * ρ.im := by
    simpa only [mul_comm] using (Complex.re_add_im ρ).symm
  have he : (1 / (((1 + nearOneEvaluationShift q : ℝ) : ℂ) - ρ)).re =
      (nearOneEvaluationShift q + (1 - ρ.re)) /
        ((nearOneEvaluationShift q + (1 - ρ.re)) ^ 2 + ρ.im ^ 2) := by
    conv_lhs => rw [hrepr, re_one_div_real_sub_complex]
    ring
  rw [he]
  have hscale : 3 / (4 * nearOneEvaluationShift q) = 3 * nearOneZeroBudget q := by
    unfold nearOneEvaluationShift
    field_simp
  rwa [hscale] at hb

/-- There cannot be two distinct actual zeros in the specified rectangle. -/
theorem nearOne_zero_unique {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ρ₁ ρ₂ : ℂ)
    (hβ₁ : 1 - nearOneZeroWidth q ≤ ρ₁.re) (ht₁ : |ρ₁.im| ≤ nearOneZeroWidth q)
    (hz₁ : DirichletCharacter.LFunction χ ρ₁ = 0)
    (hβ₂ : 1 - nearOneZeroWidth q ≤ ρ₂.re) (ht₂ : |ρ₂.im| ≤ nearOneZeroWidth q)
    (hz₂ : DirichletCharacter.LFunction χ ρ₂ = 0) : ρ₁ = ρ₂ := by
  by_contra hne
  have h₁ := nearOne_zero_reciprocal_re_ge_three_budget hq χ hχ ρ₁ hβ₁ ht₁ hz₁
  have h₂ := nearOne_zero_reciprocal_re_ge_three_budget hq χ hχ ρ₂ hβ₂ ht₂ hz₂
  have hpair := two_zero_reciprocals_re_le_localLFunctionZeroSum hq χ hχ (2 : ℂ)
    ((1 + nearOneEvaluationShift q : ℝ) : ℂ) ρ₁ ρ₂
    (by simpa using (show 1 < 1 + nearOneEvaluationShift q by have := nearOneEvaluationShift_pos q; linarith))
    hne (nearOne_zero_mem_local_disk hq χ hχ ρ₁ hβ₁ ht₁ hz₁)
    (nearOne_zero_mem_local_disk hq χ hχ ρ₂ hβ₂ ht₂ hz₂) hz₁ hz₂
  have hu := localLFunctionZeroSum_nearOne_le_five_budget hq χ hχ
  have hE := nearOneZeroBudget_pos q
  linarith

/-- The actual analytic divisor multiplicity of a zero in the rectangle is one. -/
theorem nearOne_zero_divisor_eq_one {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ)
    (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    divisor (DirichletCharacter.LFunction χ) (closedBall (2 : ℂ) (5 / 4)) ρ = 1 := by
  let D := divisor (DirichletCharacter.LFunction χ) (closedBall (2 : ℂ) (5 / 4)) ρ
  let s : ℂ := ((1 + nearOneEvaluationShift q : ℝ) : ℂ)
  have hmem := nearOne_zero_mem_local_disk hq χ hχ ρ hβ ht hzero
  have hD : 1 ≤ D := one_le_LFunction_divisor_of_zero hq χ hχ _ ρ hmem hzero
  have hr := nearOne_zero_reciprocal_re_ge_three_budget hq χ hχ ρ hβ ht hzero
  have hs : 1 < s.re := by dsimp [s]; have := nearOneEvaluationShift_pos q; linarith
  have hterm := LFunction_divisor_term_re_le_zeroSum hq χ hχ (2 : ℂ) s ρ hs
  have he : ((D : ℂ) / (s - ρ)).re = (D : ℝ) * (1 / (s - ρ)).re := by
    simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im,
      Complex.one_re, Complex.one_im]
    ring
  change ((D : ℂ) / (s - ρ)).re ≤ _ at hterm
  rw [he] at hterm
  have hu := localLFunctionZeroSum_nearOne_le_five_budget hq χ hχ
  by_contra hne
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
  have hE := nearOneZeroBudget_pos q
  change 3 * nearOneZeroBudget q ≤ (1 / (s - ρ)).re at hr
  change (localLFunctionZeroSum χ (2 : ℂ) s).re ≤ 5 * nearOneZeroBudget q at hu
  nlinarith

/-- The actual meromorphic order is one, so the preceding divisor statement
is a simple-zero assertion and cannot conceal an infinite order. -/
theorem nearOne_zero_order_eq_one {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ρ : ℂ)
    (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ = 1 := by
  have hd := nearOne_zero_divisor_eq_one hq χ hχ ρ hβ ht hzero
  have hm := nearOne_zero_mem_local_disk hq χ hχ ρ hβ ht hzero
  have ha := DirichletCharacter.differentiable_LFunction (primitive_character_ne_one hq χ hχ)
  rw [divisor_apply (fun z _ => (ha.analyticAt z).meromorphicAt) hm] at hd
  have he := WithTop.coe_untop₀_of_ne_top
    (meromorphicOrderAt_primitiveLFunction_ne_top hq χ hχ ρ)
  rw [hd] at he
  exact he.symm

/-- For a real character, conjugation and uniqueness force the possible
near-one zero to lie on the real axis. -/
theorem nearOne_zero_real_of_sq_eq_one {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ₂ : χ ^ 2 = 1)
    (ρ : ℂ) (hβ : 1 - nearOneZeroWidth q ≤ ρ.re) (ht : |ρ.im| ≤ nearOneZeroWidth q)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) : ρ.im = 0 := by
  have hzconj := LFunction_conj_zero_of_sq_eq_one χ (primitive_character_ne_one hq χ hχ) hχ₂ ρ hzero
  have heq := nearOne_zero_unique hq χ hχ ρ (starRingEnd ℂ ρ) hβ ht hzero
    (by simpa using hβ) (by simpa using ht) hzconj
  have him := congrArg Complex.im heq
  simp only [Complex.conj_im] at him
  linarith

end TwinPrime.Analytic
