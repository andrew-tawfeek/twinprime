import TwinPrime.Analytic.SiegelValue
import TwinPrime.Analytic.SiegelZeroGap

/-!
# Uniform power gaps for zeros in the logarithmic region

The Siegel value theorem supplies the value hypothesis of the existing
zero-to-value conversion. The resulting statements retain the logarithmic
region, the common positive gap constant, and the real/quadratic conclusions.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem LFunction_zero_in_log_region_power_gap :
    ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧
      ∀ (q : ℕ) [NeZero q], 1 < q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → ∀ β t : ℝ,
          1 - primitiveLogZeroFreeWidth q t ≤ β →
          DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0 →
            χ ^ 2 = 1 ∧ t = 0 ∧ d * (q : ℝ) ^ (-ε) ≤ 1 - β :=
  LFunction_zero_in_log_region_power_gap_of_value_lower_bound siegel_value_lower_bound

/-- The real-zero specialization keeps exactly the same logarithmic region
and has no supplied value lower-bound hypothesis. -/
theorem LFunction_real_zero_in_log_region_power_gap :
    ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧
      ∀ (q : ℕ) [NeZero q], 1 < q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → ∀ β : ℝ,
          1 - primitiveLogZeroFreeWidth q 0 ≤ β →
          DirichletCharacter.LFunction χ (β : ℂ) = 0 →
            χ ^ 2 = 1 ∧ d * (q : ℝ) ^ (-ε) ≤ 1 - β := by
  intro ε hε
  obtain ⟨d, hd, hgap⟩ := LFunction_zero_in_log_region_power_gap ε hε
  refine ⟨d, hd, ?_⟩
  intro q _ hq χ hχ β hβ hzero
  have h := hgap q hq χ hχ β 0 hβ (by simpa using hzero)
  exact ⟨h.1, h.2.2⟩

end TwinPrime.Analytic
