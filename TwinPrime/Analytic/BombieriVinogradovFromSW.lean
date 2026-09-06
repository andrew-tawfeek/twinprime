import TwinPrime.Analytic.SiegelWalfiszMaximal
import TwinPrime.Analytic.BVSmallConductorGrowth
import TwinPrime.Analytic.BVConductorGrowth

/-!
# Maximal Bombieri--Vinogradov from an independent small-conductor estimate

The primitive character mean, large-conductor tail, and all asymptotic
comparisons are proved inputs. Uniform centered Siegel--Walfisz remains the
single explicit distribution hypothesis of the resulting BV theorem.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

theorem MaximalSiegelWalfisz.bombieriVinogradov
    (hSW : MaximalSiegelWalfisz) : MaximalBombieriVinogradov := by
  intro A hA
  obtain ⟨C, hC, T₀, _, hsmall⟩ := hSW (2 * A + 12) (A + 10) (by linarith) (by linarith)
  obtain ⟨Ktail, hKtail, htail⟩ := eventually_bvLargeConductorBudget_le_log_saving A hA
  let K := 12 * totientReciprocalConstant * C + Ktail + 1
  have hK : 0 < K := by
    have := totientReciprocalConstant_nonneg
    dsimp [K]
    positivity
  refine ⟨A + 9, by linarith, K, hK, ?_⟩
  have hlog : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  have hfinal : ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 9) →
      (∑ q ∈ Icc 1 Q, progressionMaxError (2 * X + 2) q) ≤
        K * X / (Real.log X) ^ A := by
    filter_upwards [htail, eventually_characterExceptionBudget_le A hA,
      eventually_ge_atTop (max 256 T₀), hlog] with X ht he hX hl Q hQ
    have hX256 : 256 ≤ X := (le_max_left _ _).trans hX
    have hX2 : 2 ≤ X := by omega
    have hT₀ : T₀ ≤ 2 * X + 2 := by have := (le_max_right 256 T₀).trans hX; omega
    have hT : 256 ≤ 2 * X + 2 := by omega
    have hQbounds := bv_admissible_modulus_bounds A hA X Q hX2 (by linarith) hQ
    have hcut := bvSmallConductorCutoff_bounds A hA X hl
    let E := C * ((2 * X + 2 : ℕ) : ℝ) /
      (Real.log ((2 * X + 2 : ℕ) : ℝ)) ^ (2 * A + 12)
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hchars : ∀ r ∈ Icc 1 (bvSmallConductorCutoff A X),
        ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
          characterMaxError (2 * X + 2) χ ≤ E := by
      intro r hr χ hχ
      apply hsmall (2 * X + 2) hT₀ r (mem_Icc.mp hr).1
      · apply (show (r : ℝ) ≤ (bvSmallConductorCutoff A X : ℝ) by
          exact_mod_cast (mem_Icc.mp hr).2).trans
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
          bvSmallConductorCutoff_le_log_endpoint A hA X hX2 hl
      · exact hχ
    have hfinite := sum_progressionMaxError_le_small_conductor_budget
      (2 * X + 2) (bvSmallConductorCutoff A X) Q hT hcut.1 hQbounds.2 E hE hchars
    have hsmallBudget : totientReciprocalConstant * (1 + Real.log Q) *
        ((bvSmallConductorCutoff A X : ℝ) * E) ≤
        (12 * totientReciprocalConstant * C) * X / (Real.log X) ^ A :=
      bv_small_conductor_budget_le A hA C hC.le X Q hX2 hl hQbounds.1
    have htailBudget : totientReciprocalConstant * (1 + Real.log Q) *
        (if bvSmallConductorCutoff A X ≤ Q then
          bvLargeConductorBudget (2 * X + 2) (bvSmallConductorCutoff A X) Q else 0) ≤
        Ktail * X / (Real.log X) ^ A := by
      split_ifs with hRQ
      · exact ht (bvSmallConductorCutoff A X) Q hcut.1 hRQ hcut.2.1 hQ
      · simp only [mul_zero]
        positivity
    have herr : (Q : ℝ) * (Real.log Q +
        2 * Real.sqrt ((2 * X + 2 : ℕ) : ℝ) * Real.log ((2 * X + 2 : ℕ) : ℝ)) ≤
        (X : ℝ) / (Real.log X) ^ A := by
      have h := he Q (bv_admissible_modulus_le_exception_range A hA X Q (by linarith) hQ)
      simpa only [characterExceptionBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
    apply hfinite.trans
    calc
      _ = (totientReciprocalConstant * (1 + Real.log Q) *
          ((bvSmallConductorCutoff A X : ℝ) * E) +
          totientReciprocalConstant * (1 + Real.log Q) *
            (if bvSmallConductorCutoff A X ≤ Q then
              bvLargeConductorBudget (2 * X + 2) (bvSmallConductorCutoff A X) Q else 0)) +
          Q * (Real.log Q + 2 * Real.sqrt ((2 * X + 2 : ℕ) : ℝ) *
            Real.log ((2 * X + 2 : ℕ) : ℝ)) := by rw [mul_add]
      _ ≤ ((12 * totientReciprocalConstant * C) * X / (Real.log X) ^ A +
          Ktail * X / (Real.log X) ^ A) + (X : ℝ) / (Real.log X) ^ A :=
        add_le_add (add_le_add hsmallBudget htailBudget) herr
      _ = K * X / (Real.log X) ^ A := by dsimp [K]; ring
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨max 2 X₀, le_max_left _ _, ?_⟩
  intro X hX
  exact hX₀ X ((le_max_right _ _).trans hX)

/-- The pointwise statement suffices because its maximalization has been
proved uniformly over the growing conductor range. -/
theorem PointwiseSiegelWalfisz.bombieriVinogradov
    (hSW : PointwiseSiegelWalfisz) : MaximalBombieriVinogradov :=
  hSW.maximal.bombieriVinogradov

end TwinPrime.Analytic
