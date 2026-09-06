import TwinPrime.Analytic.CharacterCommonLevel
import TwinPrime.Analytic.LFunctionInducedValue
import TwinPrime.Analytic.LFunctionPeriodBound
import TwinPrime.Analytic.QuadraticProductLSeries
import TwinPrime.Analytic.QuadraticResidueComparison

/-!
# Comparison with a fixed auxiliary quadratic character

Induction to the product of two distinct primitive conductors costs only
logarithms at one. Together with the actual four-factor residue estimate,
this compares a second L-value with a fixed auxiliary value. Any use of an
auxiliary zero is retained as an explicit hypothesis.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The actual residue at the common product level is bounded by the two
original L-values and three logarithmic factors. The product character
is nonprincipal because the primitive conductors differ. -/
theorem norm_commonLevel_quadraticProduct_residue_le
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hq₀ : 1 < q₀) (hq : 1 < q) (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive)
    (hsq₀ : χ₀ ^ 2 = 1) (hne : q₀ ≠ q) :
    ‖regularizedQuadraticLFunctionProduct (commonLevelLeft χ₀ q)
      (commonLevelRight q₀ χ) 1‖ ≤
      5 * ‖DirichletCharacter.LFunction χ₀ 1‖ * ‖DirichletCharacter.LFunction χ 1‖ *
        (1 + Real.log (q₀ * q)) ^ 3 := by
  obtain ⟨hleft, hright⟩ := commonLevel_ne_one χ₀ χ hq₀ hq hχ₀ hχ
  have hχ₀' : χ₀ ≠ 1 := by
    intro heq
    apply hleft
    simp [commonLevelLeft, heq]
  have hχ' : χ ≠ 1 := by
    intro heq
    apply hright
    simp [commonLevelRight, heq]
  have hprod := commonLevel_mul_ne_one χ₀ χ hχ₀ hχ hsq₀ hne
  have hlog : 0 ≤ Real.log ((q₀ * q : ℕ) : ℝ) := Real.log_natCast_nonneg _
  simp only [Nat.cast_mul] at hlog
  have hleftBound : ‖DirichletCharacter.LFunction (commonLevelLeft χ₀ q) 1‖ ≤
      ‖DirichletCharacter.LFunction χ₀ 1‖ * (1 + Real.log (q₀ * q)) := by
    simpa only [commonLevelLeft, Nat.cast_mul] using
      norm_LFunction_changeLevel_one_le (Nat.dvd_mul_right q₀ q) χ₀ hχ₀'
  have hrightBound : ‖DirichletCharacter.LFunction (commonLevelRight q₀ χ) 1‖ ≤
      ‖DirichletCharacter.LFunction χ 1‖ * (1 + Real.log (q₀ * q)) := by
    simpa only [commonLevelRight, Nat.cast_mul] using
      norm_LFunction_changeLevel_one_le (Nat.dvd_mul_left q q₀) χ hχ'
  have hprodBound :
      ‖DirichletCharacter.LFunction (commonLevelLeft χ₀ q * commonLevelRight q₀ χ) 1‖ ≤
        5 * (1 + Real.log (q₀ * q)) := by
    have h := norm_LFunction_one_le_five_add_log
      (commonLevelLeft χ₀ q * commonLevelRight q₀ χ) hprod
    simp only [Nat.cast_mul] at h hlog
    linarith
  rw [regularizedQuadraticLFunctionProduct_one, norm_mul, norm_mul]
  calc
    _ ≤ (‖DirichletCharacter.LFunction χ₀ 1‖ * (1 + Real.log (q₀ * q))) *
        (‖DirichletCharacter.LFunction χ 1‖ * (1 + Real.log (q₀ * q))) *
          (5 * (1 + Real.log (q₀ * q))) := by
      gcongr
    _ = _ := by ring

/-- A zero of the auxiliary character remains an actual zero of the
four-factor product after induction to the common level. -/
theorem commonLevel_quadraticLFunctionProduct_eq_zero_of_auxiliary_zero
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : s ≠ 1) (hzero : DirichletCharacter.LFunction χ₀ s = 0) :
    quadraticLFunctionProduct (commonLevelLeft χ₀ q) (commonLevelRight q₀ χ) s = 0 := by
  have hleft : DirichletCharacter.LFunction (commonLevelLeft χ₀ q) s = 0 :=
    LFunction_changeLevel_eq_zero_of_eq_zero (Nat.dvd_mul_right q₀ q) χ₀ s hs hzero
  simp only [quadraticLFunctionProduct, hleft, mul_zero, zero_mul]

/-- A nonpositive actual product value yields an explicit lower bound for
the second primitive L-value. The auxiliary value remains in the constant. -/
theorem commonLevel_LFunction_one_lower_bound_of_nonpos
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hq₀ : 1 < q₀) (hq : 1 < q) (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive)
    (hsq₀ : χ₀ ^ 2 = 1) (hsq : χ ^ 2 = 1) (hne : q₀ ≠ q)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hF : (quadraticLFunctionProduct (commonLevelLeft χ₀ q)
      (commonLevelRight q₀ χ) (β : ℂ)).re ≤ 0) :
    (1 - β) / (20 * ‖DirichletCharacter.LFunction χ₀ 1‖ *
      residueConductorConstant ^ (1 - β) * (q₀ * q : ℝ) ^ (40 * (1 - β)) *
        (1 + Real.log (q₀ * q)) ^ 3) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  obtain ⟨hleft, hright⟩ := commonLevel_ne_one χ₀ χ hq₀ hq hχ₀ hχ
  obtain ⟨hsqLeft, hsqRight⟩ := commonLevel_sq_eq_one χ₀ χ hsq₀ hsq
  have hprod := commonLevel_mul_ne_one χ₀ χ hχ₀ hχ hsq₀ hne
  have hχ₀' : χ₀ ≠ 1 := by
    intro heq
    apply hleft
    simp [commonLevelLeft, heq]
  have haux : 0 < ‖DirichletCharacter.LFunction χ₀ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hχ₀')
  have hlog : 0 ≤ Real.log (q₀ * q : ℝ) := by
    simpa only [Nat.cast_mul] using Real.log_natCast_nonneg (q₀ * q)
  have hq₀R : (0 : ℝ) < q₀ := by exact_mod_cast (NeZero.pos q₀)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hA := residueConductorConstant_pos
  have hlower := quadraticProduct_residue_conductor_lower_bound_of_nonpos
    (commonLevelLeft χ₀ q) (commonLevelRight q₀ χ)
    hleft hright hprod hsqLeft hsqRight β hβ hβ1 hF
  have hupper := norm_commonLevel_quadraticProduct_residue_le χ₀ χ
    hq₀ hq hχ₀ hχ hsq₀ hne
  have hcomparison := hlower.trans hupper
  simp only [Nat.cast_mul] at hcomparison
  have hden : 0 < 4 * residueConductorConstant ^ (1 - β) *
      (q₀ * q : ℝ) ^ (40 * (1 - β)) := by positivity
  have hscaled := (div_le_iff₀ hden).mp hcomparison
  apply (div_le_iff₀ (by positivity)).mpr
  convert hscaled using 1
  ring

/-- A genuine zero of the fixed auxiliary character supplies the
nonpositive product hypothesis through exact induction of that zero. -/
theorem commonLevel_LFunction_one_lower_bound_of_auxiliary_zero
    {q₀ q : ℕ} [NeZero q₀] [NeZero q]
    (χ₀ : DirichletCharacter ℂ q₀) (χ : DirichletCharacter ℂ q)
    (hq₀ : 1 < q₀) (hq : 1 < q) (hχ₀ : χ₀.IsPrimitive) (hχ : χ.IsPrimitive)
    (hsq₀ : χ₀ ^ 2 = 1) (hsq : χ ^ 2 = 1) (hne : q₀ ≠ q)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₀ (β : ℂ) = 0) :
    (1 - β) / (20 * ‖DirichletCharacter.LFunction χ₀ 1‖ *
      residueConductorConstant ^ (1 - β) * (q₀ * q : ℝ) ^ (40 * (1 - β)) *
        (1 + Real.log (q₀ * q)) ^ 3) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  apply commonLevel_LFunction_one_lower_bound_of_nonpos χ₀ χ hq₀ hq hχ₀ hχ
    hsq₀ hsq hne β hβ hβ1
  have hs : (β : ℂ) ≠ 1 := by exact_mod_cast hβ1.ne
  rw [commonLevel_quadraticLFunctionProduct_eq_zero_of_auxiliary_zero χ₀ χ (β : ℂ) hs hzero]
  simp only [Complex.zero_re, le_refl]

end TwinPrime.Analytic
