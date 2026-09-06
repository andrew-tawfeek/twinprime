import TwinPrime.Analytic.SiegelValueFromComparison
import TwinPrime.Analytic.QuadraticNoZeroTransport
import TwinPrime.Analytic.QuadraticAuxiliaryCharacter

/-!
# Siegel's uniform value lower bound for primitive quadratic characters

For each positive exponent, either there is a primitive quadratic zero in
a fixed short interval below one, or all such zeros are excluded there.
In the first case its character supplies a fixed auxiliary zero. In the
second case the character of conductor four and the proved real sign
argument supply a nonpositive product. The checked residue comparison and
finite-conductor bounds then give a single positive constant for all levels.
The choice of the auxiliary zero makes no effective constant assertion.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The positive constant is uniform over all primitive quadratic characters
and all conductors greater than one. No value or zero-gap premise is assumed. -/
theorem siegel_value_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 1 < q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ^ 2 = 1 →
          c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  intro ε hε
  let δ : ℝ := min (1 / 20) (ε / 80)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδsmall : δ ≤ 1 / 20 := min_le_left _ _
  have hδε : δ ≤ ε / 80 := min_le_right _ _
  have hσ : (19 / 20 : ℝ) ≤ 1 - δ := by linarith
  have hσ1 : 1 - δ < 1 := by linarith
  by_cases hno : ∀ (r : ℕ) [NeZero r], 1 < r →
      ∀ ψ : DirichletCharacter ℂ r, ψ.IsPrimitive → ψ ^ 2 = 1 →
        ∀ u : ℝ, u ∈ Set.Ico (1 - δ) 1 → DirichletCharacter.LFunction ψ (u : ℂ) ≠ 0
  · apply exists_siegel_value_bound_of_commonLevel_nonpos auxiliaryQuadraticCharacter
      (by norm_num) auxiliaryQuadraticCharacter_isPrimitive auxiliaryQuadraticCharacter_sq_eq_one
      ε hε (1 - δ) hσ hσ1 (by linarith)
    intro q instq hq χ hχ hsq
    exact (commonLevel_quadraticLFunctionProduct_re_neg_of_primitive_interval
      (1 - δ) hσ hσ1 hno auxiliaryQuadraticCharacter χ (by norm_num) (by omega)
      auxiliaryQuadraticCharacter_isPrimitive hχ auxiliaryQuadraticCharacter_sq_eq_one hsq
      (ne_of_lt hq)).le
  · push Not at hno
    obtain ⟨q₀, instq₀, hq₀, χ₀, hχ₀, hsq₀, β, hβ, hzero⟩ := hno
    letI : NeZero q₀ := instq₀
    apply exists_siegel_value_bound_of_commonLevel_nonpos χ₀ hq₀ hχ₀ hsq₀
      ε hε β (hσ.trans hβ.1) hβ.2 (by linarith [hβ.1])
    intro q instq hq χ _hχ _hsq
    have hs : (β : ℂ) ≠ 1 := by exact_mod_cast ne_of_lt hβ.2
    rw [commonLevel_quadraticLFunctionProduct_eq_zero_of_auxiliary_zero χ₀ χ (β : ℂ) hs hzero]
    simp

end TwinPrime.Analytic
