import TwinPrime.Analytic.Decomposition
import TwinPrime.Analytic.Cutoff
import TwinPrime.Analytic.MixedCorrelation
import TwinPrime.Analytic.TypeICorrection
import TwinPrime.Analytic.MertensReduction
import TwinPrime.Analytic.PrimeToMertens
import TwinPrime.HardyLittlewood

/-!
# Conditional analytic endpoints

All estimates remain explicit hypotheses. The theorem below does not prove the
signed bilinear estimate, the mixed-correlation estimate, or the Type I estimate.
The cutoffs may vary with `X`; their finite support conditions are checked at
every sufficiently large input. Only the signed estimate is required cofinally.
The sublinear prime-power error is proved in `Correlation.lean`; the final
three-estimate version below discharges that obligation automatically.
The most refined endpoint also derives the ordinary Mertens estimate from
the named BV hypothesis. BV and the signed bilinear bound remain inputs.
-/

noncomputable section

namespace TwinPrime

open Analytic Filter

/-- The numerical budget in PLAN.md, Section 7.2. -/
theorem four_obligation_budget {A K B E W C x : ℝ}
    (hD : W = A + K + B)
    (hA : |A - C * x| ≤ C * x / 8)
    (hK : |K| ≤ C * x / 8)
    (hB : -(C * x) / 2 ≤ B)
    (hE : E ≤ C * x / 8) : C * x / 8 ≤ W - E := by
  have hAlower := (abs_le.mp hA).1
  have hKlower := (abs_le.mp hK).1
  linarith

/-- A positive proportion of the mixed main term surviving the exact signed
decomposition, after proper prime powers are removed, gives infinitely many twins.
This is a conditional theorem with all four analytic obligations visible. -/
theorem twinPrimeConjecture_of_bilinear_budget
    (U V : ℕ → ℕ) (C : ℝ) (hC : 0 < C) (X₀ : ℕ)
    (hcutoff : ∀ X ≥ X₀, 0 < U X ∧ V X ≤ X)
    (hA : ∀ X ≥ X₀, |mixedCorrelation (U X) X - C * X| ≤ C * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (U X) (V X) X| ≤ C * X / 8)
    (hE : ∀ X ≥ X₀, Epp X ≤ C * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -(C * X) / 2 ≤ bilinearTerm (U X) (V X) X) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_cofinal_W2_gt_Epp
  intro Y
  obtain ⟨X, hX, hBX⟩ := hB (max Y 1)
  have hXX₀ : X₀ ≤ X := le_trans (le_max_right _ _) hX
  have hYX : Y ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXpos : 0 < X := by omega
  have hcut := hcutoff X hXX₀
  have hbudget := four_obligation_budget
    (correlation_decomposition (U X) (V X) X hcut.1 hcut.2)
    (hA X hXX₀) (hK X hXX₀) hBX (hE X hXX₀)
  have hmain : 0 < C * (X : ℝ) / 8 := by positivity
  exact ⟨X, hYX, by linarith⟩

/-- Specialization to the existing, proved positive twin-prime constant. -/
theorem twinPrimeConjecture_of_bilinear_budget_twinConstant
    (U V : ℕ → ℕ) (X₀ : ℕ)
    (hcutoff : ∀ X ≥ X₀, 0 < U X ∧ V X ≤ X)
    (hA : ∀ X ≥ X₀,
      |mixedCorrelation (U X) X - (2 * twinPrimeConstant) * X| ≤
        (2 * twinPrimeConstant) * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (U X) (V X) X| ≤
      (2 * twinPrimeConstant) * X / 8)
    (hE : ∀ X ≥ X₀, Epp X ≤ (2 * twinPrimeConstant) * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -((2 * twinPrimeConstant) * X) / 2 ≤ bilinearTerm (U X) (V X) X) :
    TwinPrimeConjecture :=
  twinPrimeConjecture_of_bilinear_budget U V (2 * twinPrimeConstant)
    (mul_pos (by norm_num) twinPrimeConstant_pos) X₀ hcutoff hA hK hE hB

/-- The prime-power obligation is already discharged by `tendsto_Epp_div`.
The two known analytic estimates and the new signed estimate remain assumptions. -/
theorem twinPrimeConjecture_of_bilinear_estimates
    (U V : ℕ → ℕ) (C : ℝ) (hC : 0 < C) (X₀ : ℕ)
    (hcutoff : ∀ X ≥ X₀, 0 < U X ∧ V X ≤ X)
    (hA : ∀ X ≥ X₀, |mixedCorrelation (U X) X - C * X| ≤ C * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (U X) (V X) X| ≤ C * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -(C * X) / 2 ≤ bilinearTerm (U X) (V X) X) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_cofinal_W2_linear (c := C / 4) (by positivity)
  intro Y
  obtain ⟨X, hX, hBX⟩ := hB Y
  have hXX₀ : X₀ ≤ X := le_trans (le_max_right _ _) hX
  refine ⟨X, le_trans (le_max_left _ _) hX, ?_⟩
  have hcut := hcutoff X hXX₀
  have hD := correlation_decomposition (U X) (V X) X hcut.1 hcut.2
  have hAlower := (abs_le.mp (hA X hXX₀)).1
  have hKlower := (abs_le.mp (hK X hXX₀)).1
  linarith

/-- The precise primary-route endpoint: fixed fifth-root cutoffs, the existing
twin-prime constant, and only the three as-yet unproved analytic estimates. -/
theorem twinPrimeConjecture_of_primary_estimates (X₀ : ℕ)
    (hA : ∀ X ≥ X₀,
      |mixedCorrelation (primaryCutoff X) X - (2 * twinPrimeConstant) * X| ≤
        (2 * twinPrimeConstant) * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (primaryCutoff X) (primaryCutoff X) X| ≤
      (2 * twinPrimeConstant) * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_bilinear_estimates primaryCutoff primaryCutoff
    (2 * twinPrimeConstant) (mul_pos (by norm_num) twinPrimeConstant_pos) (max X₀ 1)
  · intro X hX
    have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
    exact ⟨primaryCutoff_pos hX1, primaryCutoff_le hX1⟩
  · intro X hX
    exact hA X (le_trans (le_max_left _ _) hX)
  · intro X hX
    exact hK X (le_trans (le_max_left _ _) hX)
  · intro Y
    obtain ⟨X, hX, hBX⟩ := hB (max Y 1)
    exact ⟨X, by omega, hBX⟩

/-- A refined endpoint in which the mixed estimate is derived from its named
classical distribution and smoothed Möbius/totient inputs. The Type I correction
limit and the cofinal signed bilinear bound are still explicit assumptions. -/
theorem twinPrimeConjecture_of_analytic_inputs
    (hBV : MaximalBombieriVinogradov)
    (hF : Tendsto smoothedTotientSum atTop (nhds (2 * twinPrimeConstant)))
    (hK : Tendsto (fun X : ℕ => typeICorrection (primaryCutoff X) (primaryCutoff X) X / X)
      atTop (nhds 0))
    (hB : ∀ Y : ℕ, ∃ X ≥ Y,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture := by
  have hC : 0 < 2 * twinPrimeConstant := mul_pos (by norm_num) twinPrimeConstant_pos
  have hA := eventually_mixedCorrelation_budget_of_inputs hBV hC hF
  have hK' : ∀ᶠ X : ℕ in atTop,
      |typeICorrection (primaryCutoff X) (primaryCutoff X) X| ≤
        (2 * twinPrimeConstant) * X / 8 := by
    simpa only [zero_mul, sub_zero, div_mul_eq_mul_div] using
      eventually_abs_sub_mul_le_of_tendsto_div _
        (show 0 < (2 * twinPrimeConstant) / 8 by positivity) hK
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hA.and hK')
  exact twinPrimeConjecture_of_primary_estimates X₀
    (fun X hX => (hX₀ X hX).1) (fun X hX => (hX₀ X hX).2)
    (fun Y => hB (max Y X₀))

/-- The primary route reduced to three explicit classical inputs and the open
signed bilinear bound. The mixed and Type I estimates and prime-power removal
are derived in the proof; none of these four remaining inputs is asserted here. -/
theorem twinPrimeConjecture_of_classical_inputs_and_bilinear
    (hBV : MaximalBombieriVinogradov)
    (hF : Tendsto smoothedTotientSum atTop (nhds (2 * twinPrimeConstant)))
    (hM : Tendsto (fun t : ℕ =>
      oddMoebiusTotientSum t * (Real.log ((t : ℝ) + 1)) ^ 2) atTop (nhds 0))
    (hB : ∀ Y : ℕ, ∃ X ≥ Y,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture :=
  twinPrimeConjecture_of_analytic_inputs hBV hF (tendsto_typeICorrection_div_of_inputs hBV hM) hB

/-- The ordinary Mertens estimate supplies both totient inputs and their
constants. The two classical theorems and the open signed bilinear bound
remain explicit arguments; this is not an unconditional proof. -/
theorem twinPrimeConjecture_of_bv_mertens_and_bilinear
    (hBV : MaximalBombieriVinogradov) (hM : MertensLogSix)
    (hB : ∀ Y : ℕ, ∃ X ≥ Y,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture :=
  twinPrimeConjecture_of_classical_inputs_and_bilinear hBV
    hM.tendsto_smoothed_totient hM.tendsto_odd_totient_log_sq hB

/-- BV supplies the ordinary Mertens bound and all the classical bridges.
The named distribution theorem and the open cofinal signed bilinear estimate
remain explicit hypotheses. -/
theorem twinPrimeConjecture_of_bv_and_bilinear
    (hBV : MaximalBombieriVinogradov)
    (hB : ∀ Y : ℕ, ∃ X ≥ Y,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture :=
  twinPrimeConjecture_of_bv_mertens_and_bilinear hBV hBV.mertensLogSix hB

end TwinPrime
