import TwinPrime.Analytic.ClassicalDistribution
import TwinPrime.Analytic.PrimeReciprocalReal
import TwinPrime.Analytic.MiddlePrimeSieveThreshold
import TwinPrime.Analytic.CutoffLogarithms

/-!
# A bounded reciprocal mass on a fixed middle-prime power interval

The finite comparison keeps the actual prime interval.  The eventual
constant follows from the proved reciprocal Mangoldt estimate at the real
endpoint `X^v`, with its natural floor retained exactly.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace TwinPrime.Analytic

theorem sum_middlePrime_reciprocal_le_primeReciprocalSum (U W : ℕ)
    (hU : 1 ≤ U) :
    (∑ p ∈ (Ioc U W).filter Nat.Prime, (1 : ℝ) / p) ≤
      primeReciprocalSum W / Real.log ((U : ℝ) + 1) := by
  have hlog : 0 < Real.log ((U : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < U + 1))
  apply (le_div_iff₀ hlog).mpr
  calc
    (∑ p ∈ (Ioc U W).filter Nat.Prime, (1 : ℝ) / p) * Real.log ((U : ℝ) + 1) =
        ∑ p ∈ (Ioc U W).filter Nat.Prime, Real.log ((U : ℝ) + 1) / p := by
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ (Ioc U W).filter Nat.Prime, vonMangoldt p / (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
      rw [vonMangoldt_apply_prime hpprime]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      apply Real.log_le_log (by positivity)
      exact_mod_cast (mem_Ioc.mp hpI).1
    _ ≤ primeReciprocalSum W := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpI := mem_Ioc.mp (mem_filter.mp hp).1
        exact mem_Ioc.mpr ⟨lt_of_lt_of_le (by omega : 0 < U + 1) hpI.1, hpI.2⟩
      · intro p hp hp'
        exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg p)

/-- No upper restriction on the fixed positive power is required for this
coarse reciprocal mass bound. The interval may also be empty. -/
theorem eventually_sum_middlePrime_reciprocal_le (v : ℝ) (hv : 0 < v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        (1 : ℝ) / p) ≤ M := by
  obtain ⟨c, C, hC, hcenter⟩ := maximal_bombieri_vinogradov.real_primeReciprocal_center
  refine ⟨5 * v + |c| + C, by positivity, ?_⟩
  have hpow : Tendsto (fun X : ℕ => (X : ℝ) ^ v) atTop atTop :=
    (tendsto_rpow_atTop hv).comp tendsto_natCast_atTop_atTop
  have hpowlog := (Real.tendsto_log_atTop.comp hpow).eventually (eventually_ge_atTop 1)
  have hUarg : Tendsto (fun X : ℕ => (primaryCutoff X : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop.comp tendsto_primaryCutoff)
    filter_upwards with X
    dsimp only [Function.comp_def]
    linarith
  have hUlog := (Real.tendsto_log_atTop.comp hUarg).eventually (eventually_ge_atTop 1)
  filter_upwards [hpow.eventually hcenter, hpowlog, hUlog, eventually_ge_atTop 1]
    with X hcenterX hpowlogX hUlogX hX
  dsimp only [Function.comp_def] at hpowlogX hUlogX
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hU : 1 ≤ primaryCutoff X := primaryCutoff_pos hX
  have hlogU : 0 < Real.log ((primaryCutoff X : ℝ) + 1) := by linarith
  have hlogX : Real.log (X : ℝ) ≤ 5 * Real.log ((primaryCutoff X : ℝ) + 1) := by
    have hinv : (X : ℝ) ≤ ((primaryCutoff X : ℝ) + 1) ^ (5 : ℕ) := by
      exact_mod_cast (primaryCutoff_inverse_bound X).le
    have h := Real.log_le_log hx hinv
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hrem : C / (Real.log ((X : ℝ) ^ v)) ^ 5 ≤ C :=
    div_le_self hC (one_le_pow₀ hpowlogX)
  have hrec : primeReciprocalSum (middlePrimePowerCutoff v X) ≤
      v * Real.log (X : ℝ) + |c| + C := by
    have h := (abs_le.mp hcenterX).2
    change primeReciprocalSum (middlePrimePowerCutoff v X) -
      Real.log ((X : ℝ) ^ v) - c ≤ C / (Real.log ((X : ℝ) ^ v)) ^ 5 at h
    rw [Real.log_rpow hx] at h hrem
    linarith [le_abs_self c]
  apply (sum_middlePrime_reciprocal_le_primeReciprocalSum
    (primaryCutoff X) (middlePrimePowerCutoff v X) hU).trans
  apply (div_le_iff₀ hlogU).mpr
  apply hrec.trans
  have hvlog := mul_le_mul_of_nonneg_left hlogX hv.le
  have hcscale := mul_le_mul_of_nonneg_left hUlogX (add_nonneg (abs_nonneg c) hC)
  nlinarith

end TwinPrime.Analytic
