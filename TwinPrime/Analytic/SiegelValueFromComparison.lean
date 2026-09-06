import TwinPrime.Analytic.QuadraticAuxiliaryComparison
import TwinPrime.Analytic.SiegelValuePower
import TwinPrime.Analytic.LFunctionFiniteConductors

/-!
# Uniform value bounds from an actual common-level sign condition

A fixed auxiliary character supplies the comparison at larger conductors.
The proved power absorption converts that comparison into a fixed power
lower bound, and finite-conductor nonvanishing handles the remaining levels.
The sign of the actual common-level product remains an explicit hypothesis.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- A fixed auxiliary quadratic character and an actual nonpositive-product
condition yield one positive value constant for all primitive quadratic
characters. The finite range includes the auxiliary conductor itself. -/
theorem exists_siegel_value_bound_of_commonLevel_nonpos
    {q₀ : ℕ} [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hq₀ : 1 < q₀) (hχ₀ : χ₀.IsPrimitive) (hsq₀ : χ₀ ^ 2 = 1)
    (ε : ℝ) (hε : 0 < ε) (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hδε : 1 - β ≤ ε / 80)
    (hF : ∀ (q : ℕ) [NeZero q], q₀ < q → ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → χ ^ 2 = 1 →
        (quadraticLFunctionProduct (commonLevelLeft χ₀ q)
          (commonLevelRight q₀ χ) (β : ℂ)).re ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 1 < q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  have hδ : 0 < 1 - β := sub_pos.mpr hβ1
  have hχ₀ne := primitive_character_ne_one hq₀ χ₀ hχ₀
  have hL : 0 < ‖DirichletCharacter.LFunction χ₀ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hχ₀ne)
  have hq₀R : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  let k : ℝ := siegelValuePowerConstant ε (1 - β) ‖DirichletCharacter.LFunction χ₀ 1‖
  have hk : 0 < k := siegelValuePowerConstant_pos ε (1 - β)
    ‖DirichletCharacter.LFunction χ₀ 1‖ hε hδ hL
  obtain ⟨c₀, hc₀, hfinite⟩ := exists_pos_le_norm_LFunction_one_of_conductor_le q₀
  let c : ℝ := min c₀ (k * (q₀ : ℝ) ^ (-ε))
  have hc : 0 < c := lt_min hc₀ (mul_pos hk (Real.rpow_pos_of_pos hq₀R _))
  refine ⟨c, hc, ?_⟩
  intro q instq hq χ hχ hsq
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hp : 0 ≤ (q : ℝ) ^ (-ε) := Real.rpow_nonneg hqR.le _
  by_cases hsmall : q ≤ q₀
  · have hp1 : (q : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (show 1 ≤ q by omega)) (neg_nonpos.mpr hε.le)
    calc
      _ ≤ c := mul_le_of_le_one_right hc.le hp1
      _ ≤ c₀ := min_le_left _ _
      _ ≤ _ := hfinite q hsmall χ (primitive_character_ne_one hq χ hχ)
  · have hlarge : q₀ < q := Nat.lt_of_not_ge hsmall
    have hQ : (1 : ℝ) ≤ (q₀ : ℝ) * (q : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (NeZero.ne q₀) (NeZero.ne q)))
    have hpower := siegelValuePowerConstant_mul_rpow_le ε (1 - β)
      ‖DirichletCharacter.LFunction χ₀ 1‖ ((q₀ : ℝ) * (q : ℝ))
      hε hδ hL hδε hQ
    have hcomparison := commonLevel_LFunction_one_lower_bound_of_nonpos
      χ₀ χ hq₀ hq hχ₀ hχ hsq₀ hsq hlarge.ne β hβ hβ1 (hF q hlarge χ hχ hsq)
    calc
      _ ≤ (k * (q₀ : ℝ) ^ (-ε)) * (q : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hp
      _ = k * ((q₀ : ℝ) * (q : ℝ)) ^ (-ε) := by
        rw [Real.mul_rpow hq₀R.le hqR.le]
        ring
      _ ≤ _ := hpower.trans hcomparison

end TwinPrime.Analytic
