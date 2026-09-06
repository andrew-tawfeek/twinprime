import TwinPrime.Analytic.LargePrimeModuli
import TwinPrime.Analytic.MiddlePrimeSieveDenominator
import TwinPrime.Analytic.SquarefreeWeightedDistribution

/-!
# Aggregating the actual middle-prime Selberg remainder

Every modulus is squarefree and has a unique largest prime. This preserves
the Selberg weight and embeds the complete error in the squarefree-weighted
progression sum, to which the proved weighted distribution theorem applies.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace TwinPrime.Analytic

open TwinPrime.Sieve

def middlePrimeSieveErrorMass (U W Y : ℕ) (z : ℕ → ℕ) : ℝ :=
  ∑ q ∈ (Ioc U W).filter Nat.Prime,
    ∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
      (3 : ℝ) ^ ω d * progressionMaxError Y (q * d)

theorem middlePrimeSieveErrorMass_nonneg (U W Y : ℕ) (z : ℕ → ℕ) :
    0 ≤ middlePrimeSieveErrorMass U W Y z :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    mul_nonneg (by positivity) (progressionMaxError_nonneg _ _)

/-- The entire remainder is embedded into one squarefree weighted error
sum. In particular no replacement of `3^ω(d)` by a constant occurs. -/
theorem middlePrimeSieveErrorMass_le_weighted (U W D Y : ℕ) (z : ℕ → ℕ)
    (hU : 2 ≤ U)
    (hz : ∀ q ∈ Ioc U W, q.Prime → z q < q ∧ q * z q ^ 2 ≤ D) :
    middlePrimeSieveErrorMass U W Y z ≤
      squarefreeWeightedProgressionError (oddPrimorial D) D Y := by
  classical
  let E : ℕ → ℝ := fun m =>
    if m ∣ oddPrimorial D then (3 : ℝ) ^ ω m * progressionMaxError Y m else 0
  have hE : ∀ m, 0 ≤ E m := by
    intro m
    dsimp [E]
    split_ifs
    · exact mul_nonneg (by positivity) (progressionMaxError_nonneg Y m)
    · exact le_rfl
  have hinner (q : ℕ) (hqmem : q ∈ (Ioc U W).filter Nat.Prime) :
      (∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
        (3 : ℝ) ^ ω d * progressionMaxError Y (q * d)) ≤
        ∑ d ∈ (Icc 1 (D / q)).filter
          (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q), E (q * d) := by
    obtain ⟨hqI, hq⟩ := mem_filter.mp hqmem
    obtain ⟨hzq, hlevel⟩ := hz q hqI hq
    have hqodd : Odd q := hq.odd_of_ne_two (by have := (mem_Ioc.mp hqI).1; omega)
    have hsub : (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2) ⊆
        (Icc 1 (D / q)).filter (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q) := by
      intro d hd
      obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, ?_⟩, ?_⟩
      · apply (Nat.le_div_iff_mul_le hq.pos).mpr
        simpa only [mul_comm] using (Nat.mul_le_mul_left q hdz).trans hlevel
      · intro p hp hpd
        exact (((prime_dvd_oddPrimorial_iff hp).mp
          (hpd.trans (Nat.dvd_of_mem_divisors hdP))).2).trans_lt hzq
    calc
      _ ≤ ∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
          E (q * d) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        have hdiv := Nat.dvd_of_mem_divisors hdP
        have hqd := prime_coprime_of_dvd_oddPrimorial q (z q) d hq hzq hdiv
        have hdodd : Odd d := Nat.not_even_iff_odd.mp
          (fun h => not_two_dvd_of_dvd_oddPrimorial hdiv h.two_dvd)
        have hsq : Squarefree (q * d) := (Nat.squarefree_mul hqd).mpr
          ⟨hq.squarefree, (oddPrimorial_squarefree (z q)).squarefree_of_dvd hdiv⟩
        have hle : q * d ≤ D := (Nat.mul_le_mul_left q hdz).trans hlevel
        have hmP := dvd_oddPrimorial_of_odd_squarefree_le (q * d) D
          (hqodd.mul hdodd) hsq hle
        dsimp [E]
        rw [if_pos hmP]
        apply mul_le_mul_of_nonneg_right _ (progressionMaxError_nonneg Y (q * d))
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        rw [cardDistinctFactors_mul hqd, cardDistinctFactors_apply_prime hq]
        omega
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hE (q * d))
  calc
    _ ≤ ∑ q ∈ (Ioc U W).filter Nat.Prime,
        ∑ d ∈ (Icc 1 (D / q)).filter
          (fun d => ∀ p, Nat.Prime p → p ∣ d → p < q), E (q * d) :=
      sum_le_sum hinner
    _ ≤ ∑ m ∈ Icc 1 D, E m :=
      sum_largest_prime_modulus_multiples_le U W D E (fun m _ => hE m)
    _ = _ := by
      dsimp only [E, squarefreeWeightedProgressionError]
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext m
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hm1, hmD⟩, hmP⟩
        exact ⟨⟨hmP, oddPrimorial_ne_zero D⟩, hmD⟩
      · rintro ⟨⟨hmP, _⟩, hmD⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hmP
          (Nat.pos_of_ne_zero (oddPrimorial_ne_zero D)), hmD⟩, hmP⟩

/-- The complete negative-class mass is bounded by an explicit scalar main
sum and the same total error whose all-log convergence is proved below. -/
theorem middlePrimeMass_le_main_add_errorMass (U W X : ℕ) (z : ℕ → ℕ)
    (hU : 2 ≤ U) (hWX : W ≤ 2 * X) (hzpos : ∀ q, 1 ≤ z q)
    (hz : ∀ q ∈ Ioc U W, q.Prime → z q < q ∧ z q ≤ W) :
    middlePrimeMass U W X ≤
      (∑ q ∈ (Ioc U W).filter Nat.Prime,
        Real.log ((2 * X : ℝ) / q) *
          (((X : ℝ) / Nat.totient q) / middlePrimeSelbergDenominator (z q))) +
      2 * Real.log (2 * X + 2) * middlePrimeSieveErrorMass U W (2 * X + 2) z := by
  classical
  let e : ℕ → ℝ := fun q =>
    ∑ d ∈ (oddPrimorial (z q)).divisors.filter (fun d => d ≤ z q ^ 2),
      (3 : ℝ) ^ ω d * progressionMaxError (2 * X + 2) (q * d)
  have he0 : ∀ q, 0 ≤ e q := fun q => sum_nonneg fun d _ =>
    mul_nonneg (by positivity) (progressionMaxError_nonneg _ _)
  have heq (q : ℕ) :
      (∑ d ∈ (oddPrimorial (z q)).divisors,
        if (d : ℝ) ≤ (z q : ℝ) ^ 2 then
          (3 : ℝ) ^ ω d * progressionMaxError (2 * X + 2) (q * d) else 0) = e q := by
    dsimp [e]
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    have hiff : (d : ℝ) ≤ (z q : ℝ) ^ 2 ↔ d ≤ z q ^ 2 := by norm_cast
    simp only [hiff]
  calc
    _ ≤ ∑ q ∈ (Ioc U W).filter Nat.Prime,
        Real.log ((2 * X : ℝ) / q) *
          (((X : ℝ) / Nat.totient q) / middlePrimeSelbergDenominator (z q) + 2 * e q) := by
      simpa only [middlePrimeSieve_selbergBoundingSum_eq, heq] using
        middlePrimeMass_le_selberg_bound U W X z hU hWX hzpos hz
    _ ≤ ∑ q ∈ (Ioc U W).filter Nat.Prime,
        (Real.log ((2 * X : ℝ) / q) *
          (((X : ℝ) / Nat.totient q) / middlePrimeSelbergDenominator (z q)) +
          (2 * Real.log (2 * X + 2)) * e q) := by
      apply sum_le_sum
      intro q hqmem
      obtain ⟨hqI, hq⟩ := mem_filter.mp hqmem
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
      have hqX : (q : ℝ) ≤ 2 * X := by exact_mod_cast (mem_Ioc.mp hqI).2.trans hWX
      have hLX : Real.log ((2 * X : ℝ) / q) ≤ Real.log (2 * X + 2) := by
        apply Real.log_le_log (div_pos (lt_of_lt_of_le hqpos hqX) hqpos)
        exact (div_le_self (by positivity) hq1).trans (by linarith)
      nlinarith [he0 q]
    _ = _ := by rw [sum_add_distrib, ← mul_sum]; rfl

/-- The complete weighted Selberg error is negligible after every fixed
logarithmic loss at a fixed power level below one half. -/
theorem tendsto_log_pow_mul_middlePrimeSieveErrorMass_div
    (U W D : ℕ → ℕ) (z : ℕ → ℕ → ℕ) (a : ℝ) (ha : a < 1 / 2)
    (hU : ∀ᶠ X : ℕ in atTop, 2 ≤ U X)
    (hD : ∀ᶠ X : ℕ in atTop, (D X : ℝ) ≤ (X : ℝ) ^ a)
    (hz : ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (U X) (W X), q.Prime →
      z X q < q ∧ q * z X q ^ 2 ≤ D X) (k : ℕ) :
    Tendsto (fun X : ℕ => Real.log (2 * X + 2) ^ k *
      middlePrimeSieveErrorMass (U X) (W X) (2 * X + 2) (z X) / X)
      atTop (nhds 0) := by
  have hweighted := tendsto_log_pow_mul_squarefreeWeightedProgressionError_div_of_power_level
    (fun X => oddPrimorial (D X)) D (fun X => oddPrimorial_squarefree (D X)) a ha hD k
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hweighted
  · filter_upwards with X
    have hlog : 0 ≤ Real.log (2 * (X : ℝ) + 2) := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) X
      linarith)
    exact div_nonneg (mul_nonneg (pow_nonneg hlog k)
      (middlePrimeSieveErrorMass_nonneg _ _ _ _)) (Nat.cast_nonneg X)
  · filter_upwards [hU, hz] with X hUX hzX
    have hlog : 0 ≤ Real.log (2 * (X : ℝ) + 2) := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) X
      linarith)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (middlePrimeSieveErrorMass_le_weighted (U X) (W X) (D X) (2 * X + 2) (z X) hUX hzX)
      (pow_nonneg hlog k)) (Nat.cast_nonneg X)

end TwinPrime.Analytic
