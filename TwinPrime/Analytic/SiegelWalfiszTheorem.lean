import TwinPrime.Analytic.CenteredUnsmoothing

/-!
# The centered Siegel--Walfisz theorem

The stronger smoothed theorem is applied at both endpoints of the finite
difference. The second endpoint is larger, so it satisfies the same
threshold and the same conductor bound. Restriction to natural endpoints
gives the exact proposition used by the distribution assembly.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

theorem real_siegel_walfisz (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ‖centeredRealCharacterPsi x χ‖ ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨C, hC, hsmoothed⟩ := smoothed_siegel_walfisz (2 * A + 4) B (by linarith) hB
  obtain ⟨X, hX⟩ := eventually_atTop.mp hsmoothed
  refine ⟨5 * C + 5, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_log_rpow_le_self (A + 2)] with x hxX hx hlog hpow
  intro q hq hqL χ hχ
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  let y := x + x / (Real.log x) ^ (A + 2)
  have hxy : x ≤ y := by
    have hh : 0 ≤ x / (Real.log x) ^ (A + 2) := by positivity
    dsimp [y]
    linarith
  have hqLy : (q : ℝ) ≤ (Real.log y) ^ B :=
    hqL.trans (Real.rpow_le_rpow hL0.le (Real.log_le_log hx0 hxy) hB.le)
  exact norm_centeredRealCharacterPsi_le_of_two_smoothed χ A C x hA hC hx hlog hpow
    (hX x hxX q hq hqL χ hχ) (hX y (hxX.trans hxy) q hq hqLy χ hχ)

/-- The independent, fully centered small-conductor estimate. Its
constants may be ineffective because the proved Siegel bound is ineffective. -/
theorem pointwise_siegel_walfisz : PointwiseSiegelWalfisz := by
  intro A B hA hB
  obtain ⟨C, hC, hreal⟩ := real_siegel_walfisz A B hA hB
  have hnat : ∀ᶠ T : ℕ in atTop,
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log (T : ℝ)) ^ B →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ‖centeredRealCharacterPsi (T : ℝ) χ‖ ≤ C * T / (Real.log (T : ℝ)) ^ A :=
    tendsto_natCast_atTop_atTop.eventually hreal
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnat
  refine ⟨C, hC, max 2 N, le_max_left _ _, ?_⟩
  intro T hT q hq hqL χ hχ
  rw [← centeredRealCharacterPsi_natCast T χ]
  exact hN T ((le_max_right 2 N).trans hT) q hq hqL χ hχ

end TwinPrime.Analytic
