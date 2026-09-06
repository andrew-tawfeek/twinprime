import TwinPrime.Analytic.LFunctionNonquadraticZeroFree
import TwinPrime.Analytic.ZetaLocalExpansion

/-!

# Quadratic-character zero exclusion away from small heights

The square character is principal, so its zeta pole is retained in the
three-four-one inequality. A height condition bounds that extra pole term.
The possible real zero near one is outside the scope of this theorem.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The real part of the principal pole at twice the height. -/
theorem principal_pole_re_at_twice_height (a t : ℝ) :
    (1 / ((a : ℂ) + Complex.I * (2 * t : ℝ))).re = a / (a ^ 2 + 4 * t ^ 2) := by
  simp only [Complex.div_re, Complex.normSq_apply, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem principal_pole_re_le_one_fifth (a t : ℝ) (ha : 0 < a) (ht : a ≤ |t|) :
    (1 / ((a : ℂ) + Complex.I * (2 * t : ℝ))).re ≤ 1 / (5 * a) := by
  rw [principal_pole_re_at_twice_height]
  have hsq : a ^ 2 ≤ t ^ 2 := by
    have h := mul_self_le_mul_self ha.le ht
    nlinarith [sq_abs t]
  apply (div_le_div_iff₀ (by positivity : 0 < a ^ 2 + 4 * t ^ 2)
    (by positivity : 0 < 5 * a)).mpr
  nlinarith

/-- The numerical contradiction after retaining and bounding the extra pole. -/
theorem four_three_one_fifth_pole_contradiction {E δ : ℝ} (hE : 0 < E)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (40 * E)) :
    ¬ 4 / (1 / (4 * E) + δ) ≤
      3 / (1 / (4 * E)) + 1 / (5 * (1 / (4 * E))) + E := by
  have ha : 0 < 1 / (4 * E) := by positivity
  have hden : 0 < 1 / (4 * E) + δ := by linarith
  have hsum : 1 / (4 * E) + 1 / (40 * E) = 11 / (40 * E) := by field_simp; ring
  have hbound : 1 / (4 * E) + δ ≤ 11 / (40 * E) := by linarith
  have hlo : 160 * E / 11 ≤ 4 / (1 / (4 * E) + δ) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 160 * E / 11)
    have heq : (160 * E / 11) * (11 / (40 * E)) = 4 := by field_simp; ring
    linarith
  have hr : 3 / (1 / (4 * E)) + 1 / (5 * (1 / (4 * E))) + E = 69 * E / 5 := by
    field_simp
    ring
  rw [hr]
  linarith

def quadraticZeroFreeBudget (q : ℕ) (t : ℝ) : ℝ :=
  120 + 4 * primitiveLFunctionLogBudget q t + zetaLogBudget (2 * t) + Real.log q

theorem quadraticZeroFreeBudget_ge (q : ℕ) (t : ℝ) :
    120 ≤ quadraticZeroFreeBudget q t := by
  have hK := primitiveLFunctionLogBudget_nonneg q t
  have hZ := zetaLogBudget_nonneg (2 * t)
  have hq := Real.log_natCast_nonneg q
  unfold quadraticZeroFreeBudget
  linarith

/-- Three-four-one for an actual quadratic-character zero keeps the entire
principal pole contribution at the doubled height. -/
theorem four_div_sub_le_of_quadratic_zero {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1)
    (β t σ : ℝ) (hβ : 3 / 4 ≤ β) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    4 / (σ - β) ≤ 3 / (σ - 1) +
      (1 / ((σ : ℂ) - 1 + Complex.I * (2 * t : ℝ))).re + quadraticZeroFreeBudget q t := by
  have hp := three_four_one_LFunction_logDerivative_nonneg χ hσ t
  rw [hχ2] at hp
  have hz := neg_zeta_logDerivative_real_le_pole_add_forty σ hσ hσu
  have hfirst := neg_logDerivative_LFunction_re_le_budget_sub_one_div_of_zero
    hq χ hχ β t σ hβ hσ hσu hzero
  have hsecond := neg_logDerivative_LFunction_principal_re_le_zeta_add_log q
    ((σ : ℂ) + Complex.I * (2 * t : ℝ)) (by simpa using hσ)
  have hzt := neg_logDerivative_zeta_re_le_pole_add_budget σ (2 * t) hσ hσu
  rw [show 4 / (σ - β) = 4 * (1 / (σ - β)) by ring,
    show 3 / (σ - 1) = 3 * (1 / (σ - 1)) by ring]
  unfold quadraticZeroFreeBudget
  linarith

/-- Any larger budget gives a compatible width and height threshold.
This permits a common budget in the different character and height branches. -/
theorem LFunction_ne_zero_of_quadratic_large_height_of_budget {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1)
    (β t E : ℝ) (hbudget : quadraticZeroFreeBudget q t ≤ E)
    (hβ : 1 - 1 / (40 * E) ≤ β) (ht : 1 / (4 * E) ≤ |t|) :
    DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) ≠ 0 := by
  intro hzero
  let a : ℝ := 1 / (4 * E)
  have hE : 120 ≤ E := (quadraticZeroFreeBudget_ge q t).trans hbudget
  have hE0 : 0 < E := by linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hau : a ≤ 1 / 8 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 4 * E)).mpr
    linarith
  have heps : 1 / (40 * E) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 40 * E)).mpr
    linarith
  have hβ1 : β < 1 := by
    simpa using primitiveLFunction_zero_re_lt_one hq χ hχ
      ((β : ℂ) + Complex.I * t) hzero
  have hδ : 1 - β ≤ 1 / (40 * E) := by linarith
  have hβlow : 3 / 4 ≤ β := by linarith
  have hσ : 1 < 1 + a := by linarith
  have hσu : 1 + a ≤ 9 / 8 := by linarith
  have hineq := four_div_sub_le_of_quadratic_zero hq χ hχ hχ2 β t (1 + a)
    hβlow hσ hσu hzero
  have hshift : ((1 + a : ℝ) : ℂ) - 1 + Complex.I * (2 * t : ℝ) =
      (a : ℂ) + Complex.I * (2 * t : ℝ) := by push_cast; ring
  rw [show 1 + a - β = a + (1 - β) by ring, add_sub_cancel_left, hshift] at hineq
  have hpole := principal_pole_re_le_one_fifth a t ha0 ht
  have hbad : 4 / (a + (1 - β)) ≤ 3 / a + 1 / (5 * a) + E := by
    linarith
  exact four_three_one_fifth_pole_contradiction hE0 (by linarith) hδ hbad

/-- An explicit zero-free region for primitive quadratic characters at
heights outside the stated small interval. No assertion about a real
exceptional zero is made. -/
theorem LFunction_ne_zero_of_quadratic_large_height {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1)
    (β t : ℝ) (hβ : 1 - 1 / (40 * quadraticZeroFreeBudget q t) ≤ β)
    (ht : 1 / (4 * quadraticZeroFreeBudget q t) ≤ |t|) :
    DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) ≠ 0 :=
  LFunction_ne_zero_of_quadratic_large_height_of_budget hq χ hχ hχ2 β t
    (quadraticZeroFreeBudget q t) le_rfl hβ ht

end TwinPrime.Analytic
