import TwinPrime.Analytic.MiddlePrimeSieveMass
import TwinPrime.Analytic.HarmonicConvolutionLimit
import TwinPrime.Analytic.MiddlePrimeSieveError

/-!
# Asymptotic size of the middle-prime sieve denominator

Absolute convergence of the correction and the exact harmonic convolution
give `S(z) / log z → 1 / (2 C₂)`. The reciprocal form is uniform over all
sufficiently large natural thresholds, for substitution into a growing
family of finite sieves.
-/

noncomputable section

open Finset Filter Topology

namespace TwinPrime.Analytic

theorem tendsto_middlePrimeSelbergDenominator_div_one_add_log :
    Tendsto (fun z : ℕ => middlePrimeSelbergDenominator z / (1 + Real.log z))
      atTop (𝓝 (1 / (2 * twinPrimeConstant))) := by
  have h := tendsto_harmonic_convolution_div_log_of_zero
    middlePrimeSelbergCorrection
    (by simpa only [Real.norm_eq_abs] using summable_norm_middlePrimeSelbergCorrection)
    (ArithmeticFunction.map_zero (f := middlePrimeSelbergCorrection))
  simpa only [← middlePrimeSelbergDenominator_eq_harmonic_convolution,
    tsum_middlePrimeSelbergCorrection] using h

theorem tendsto_middlePrimeSelbergDenominator_div_log :
    Tendsto (fun z : ℕ => middlePrimeSelbergDenominator z / Real.log z)
      atTop (𝓝 (1 / (2 * twinPrimeConstant))) := by
  have hlog : Tendsto (fun z : ℕ => Real.log (z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun z : ℕ => (1 + Real.log z) / Real.log z)
      atTop (𝓝 1) := by
    have h := hlog.inv_tendsto_atTop.add_const 1
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with z hz
    have hz1 : (1 : ℝ) < z := by exact_mod_cast hz
    have hn : Real.log (z : ℝ) ≠ 0 := (Real.log_pos hz1).ne'
    change (Real.log (z : ℝ))⁻¹ + 1 = _
    simp only [add_div, one_div, div_self hn]
  have h := tendsto_middlePrimeSelbergDenominator_div_one_add_log.mul hratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with z hz
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hn : 1 + Real.log (z : ℝ) ≠ 0 := by
    have := Real.log_nonneg hz1
    linarith
  field_simp

theorem tendsto_log_div_middlePrimeSelbergDenominator :
    Tendsto (fun z : ℕ => Real.log z / middlePrimeSelbergDenominator z)
      atTop (𝓝 (2 * twinPrimeConstant)) := by
  have hC : 2 * twinPrimeConstant ≠ 0 :=
    (mul_pos (by norm_num) twinPrimeConstant_pos).ne'
  have h := tendsto_middlePrimeSelbergDenominator_div_log.inv₀ (one_div_ne_zero hC)
  simpa only [inv_div, inv_one, div_one] using h

/-- One threshold controls every member of a growing sieve family. -/
theorem middlePrimeSelbergDenominator_uniform_reciprocal_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : ℕ, ∀ z ≥ Z, 0 < Real.log (z : ℝ) ∧
      1 / middlePrimeSelbergDenominator z ≤
        (2 * twinPrimeConstant + ε) / Real.log z := by
  have h := tendsto_log_div_middlePrimeSelbergDenominator.eventually
    (gt_mem_nhds (lt_add_of_pos_right (2 * twinPrimeConstant) hε))
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp h
  refine ⟨max Z 2, fun z hz => ?_⟩
  have hz2 : 2 ≤ z := (le_max_right _ _).trans hz
  have hz1 : (1 : ℝ) < z := by exact_mod_cast hz2
  have hlog := Real.log_pos hz1
  refine ⟨hlog, ?_⟩
  have hr := (hZ z ((le_max_left _ _).trans hz)).le
  calc
    1 / middlePrimeSelbergDenominator z =
        (Real.log z / middlePrimeSelbergDenominator z) / Real.log z := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hr hlog.le

/-- The reciprocal asymptotic can be substituted simultaneously into every
active sieve when the smallest active threshold tends to infinity. -/
theorem eventually_middlePrimeMass_le_log_main_add_errorMass
    (U W : ℕ → ℕ) (z : ℕ → ℕ → ℕ)
    (hU : ∀ᶠ X : ℕ in atTop, 2 ≤ U X)
    (hWX : ∀ᶠ X : ℕ in atTop, W X ≤ 2 * X)
    (hzpos : ∀ᶠ X : ℕ in atTop, ∀ q, 1 ≤ z X q)
    (hz : ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (U X) (W X), q.Prime →
      z X q < q ∧ z X q ≤ W X)
    (hzlarge : ∀ Z : ℕ, ∀ᶠ X : ℕ in atTop,
      ∀ q ∈ Ioc (U X) (W X), q.Prime → Z ≤ z X q)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, middlePrimeMass (U X) (W X) X ≤
      (2 * twinPrimeConstant + ε) *
        (∑ q ∈ (Ioc (U X) (W X)).filter Nat.Prime,
          Real.log ((2 * X : ℝ) / q) * (((X : ℝ) / Nat.totient q) / Real.log (z X q))) +
      2 * Real.log (2 * X + 2) *
        middlePrimeSieveErrorMass (U X) (W X) (2 * X + 2) (z X) := by
  classical
  obtain ⟨Z, hZ⟩ := middlePrimeSelbergDenominator_uniform_reciprocal_bound ε hε
  filter_upwards [hU, hWX, hzpos, hz, hzlarge Z] with X hUX hWX hzposX hzX hzlargeX
  apply (middlePrimeMass_le_main_add_errorMass (U X) (W X) X (z X)
    hUX hWX hzposX hzX).trans
  refine add_le_add ?_ le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro q hqmem
  obtain ⟨hqI, hq⟩ := mem_filter.mp hqmem
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hqX : (q : ℝ) ≤ 2 * X := by exact_mod_cast (mem_Ioc.mp hqI).2.trans hWX
  have hlog : 0 ≤ Real.log ((2 * X : ℝ) / q) :=
    Real.log_nonneg ((one_le_div hqpos).mpr hqX)
  have hmain : 0 ≤ (X : ℝ) / Nat.totient q := by positivity
  have hb := mul_le_mul_of_nonneg_left (hZ (z X q) (hzlargeX q hqI hq)).2
    (mul_nonneg hlog hmain)
  convert! hb using 1 <;> ring

end TwinPrime.Analytic
