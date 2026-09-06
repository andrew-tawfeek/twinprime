import TwinPrime.Analytic.MiddlePrimeSieveThreshold
import TwinPrime.Analytic.MiddlePrimeSieveAsymptotic

/-!
# The actual power-cutoff middle-prime sieve

The explicit integer thresholds satisfy the geometric conditions of the
finite sieve. The entire weighted remainder is negligible, and the
remaining normalized upper bound has one explicit prime main sum.
-/

noncomputable section

open Finset Filter Topology

namespace TwinPrime.Analytic

def middlePrimePowerMainSum (a v : ℝ) (X : ℕ) : ℝ :=
  ∑ q ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
    Real.log ((2 * X : ℝ) / q) /
      ((Nat.totient q : ℝ) * Real.log (middlePrimeSieveThreshold a X q))

theorem middlePrimePowerCutoff_le_input (v : ℝ) (hv : v ≤ 1)
    (X : ℕ) (hX : 1 ≤ X) : middlePrimePowerCutoff v X ≤ X := by
  apply Nat.floor_le_of_le
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hX) hv

/-- The full weighted remainder for the actual thresholds is negligible
after every fixed logarithmic loss. -/
theorem tendsto_log_pow_mul_middlePrimePowerSieveError_div
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) (k : ℕ) :
    Tendsto (fun X : ℕ => Real.log (2 * X + 2) ^ k *
      middlePrimeSieveErrorMass (primaryCutoff X) (middlePrimePowerCutoff v X)
        (2 * X + 2) (middlePrimeSieveThreshold a X) / X)
      atTop (𝓝 0) := by
  apply tendsto_log_pow_mul_middlePrimeSieveErrorMass_div primaryCutoff
    (middlePrimePowerCutoff v) (middlePrimePowerCutoff a)
    (middlePrimeSieveThreshold a) a ha
  · filter_upwards [eventually_ge_atTop 32] with X hX
    exact primaryCutoff_two_le hX
  · filter_upwards with X
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) a)
  · filter_upwards [eventually_middlePrimeSieveThreshold_support a v hv hva ha]
      with X hX q hq _
    exact ⟨(hX q hq).1, (hX q hq).2.2⟩

theorem tendsto_middlePrimePowerSieveFullError_div
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    Tendsto (fun X : ℕ => 2 * Real.log (2 * X + 2) *
      middlePrimeSieveErrorMass (primaryCutoff X) (middlePrimePowerCutoff v X)
        (2 * X + 2) (middlePrimeSieveThreshold a X) / X)
      atTop (𝓝 0) := by
  have h := (tendsto_log_pow_mul_middlePrimePowerSieveError_div a v hv hva ha 1).const_mul 2
  simp only [pow_one, mul_zero] at h
  convert! h using 1
  ext X
  ring

/-- The denominator asymptotic and all geometric hypotheses are supplied
for the actual power-cutoff family. -/
theorem eventually_middlePrimePowerMass_div_le_main_add_error
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      middlePrimeMass (primaryCutoff X) (middlePrimePowerCutoff v X) X / (X : ℝ) ≤
        (2 * twinPrimeConstant + ε) * middlePrimePowerMainSum a v X +
          2 * Real.log (2 * X + 2) *
            middlePrimeSieveErrorMass (primaryCutoff X) (middlePrimePowerCutoff v X)
              (2 * X + 2) (middlePrimeSieveThreshold a X) / X := by
  classical
  have hU : ∀ᶠ X : ℕ in atTop, 2 ≤ primaryCutoff X := by
    filter_upwards [eventually_ge_atTop 32] with X hX
    exact primaryCutoff_two_le hX
  have hW : ∀ᶠ X : ℕ in atTop, middlePrimePowerCutoff v X ≤ 2 * X := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact (middlePrimePowerCutoff_le_input v (by linarith) X hX).trans (by omega)
  have hz : ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X), q.Prime →
        middlePrimeSieveThreshold a X q < q ∧
          middlePrimeSieveThreshold a X q ≤ middlePrimePowerCutoff v X := by
    filter_upwards [eventually_middlePrimeSieveThreshold_support a v hv hva ha]
      with X hX q hq _
    exact ⟨(hX q hq).1, (hX q hq).2.1⟩
  have hlarge : ∀ Z : ℕ, ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X), q.Prime →
        Z ≤ middlePrimeSieveThreshold a X q := by
    intro Z
    filter_upwards [eventually_middlePrimeSieveThreshold_active_ge a v hv hva Z]
      with X hX q hq _
    exact hX q hq
  have h := eventually_middlePrimeMass_le_log_main_add_errorMass primaryCutoff
    (middlePrimePowerCutoff v) (middlePrimeSieveThreshold a) hU hW
    (Filter.Eventually.of_forall (fun X q => middlePrimeSieveThreshold_pos a X q))
    hz hlarge ε hε
  filter_upwards [h, eventually_ge_atTop 1] with X hX hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hmain : (∑ q ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        Real.log ((2 * X : ℝ) / q) *
          (((X : ℝ) / Nat.totient q) / Real.log (middlePrimeSieveThreshold a X q))) =
      (X : ℝ) * middlePrimePowerMainSum a v X := by
    rw [middlePrimePowerMainSum, mul_sum]
    apply sum_congr rfl
    intro q _
    ring
  rw [hmain] at hX
  have hdiv := div_le_div_of_nonneg_right hX hXpos.le
  convert! hdiv using 1
  field_simp

end TwinPrime.Analytic
