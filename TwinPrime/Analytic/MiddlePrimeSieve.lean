import TwinPrime.Analytic.MixedPrimeBetaSmallPart
import TwinPrime.Analytic.PrimeDistribution
import TwinPrime.Analytic.TotientReciprocal
import TwinPrime.Sieve.TwinSieve

/-!
# A Selberg upper sieve inside a prime-divisor progression

The support consists of multiples of a fixed prime `q` in the actual dyadic
interval, weighted by `Λ(n+2)`. Sifting below `q` gives the ordinary reciprocal
totient density. Its remainder is the actual progression error at `q*d`.
-/

noncomputable section

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.omega

namespace TwinPrime.Analytic

open TwinPrime.Sieve

/-- The shifted-prime sieve restricted to multiples of `q`. The restriction
`z < q` is needed for the remainder formula, not to define the sieve. -/
def middlePrimeSieve (q X z : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Ioc X (2 * X)).filter (q ∣ ·)
  prodPrimes := oddPrimorial z
  prodPrimes_squarefree := oddPrimorial_squarefree z
  weights := fun n => vonMangoldt (n + 2)
  weights_nonneg := fun n => vonMangoldt_nonneg
  totalMass := (X : ℝ) / Nat.totient q
  nu := reciprocalTotient
  nu_mult := isMultiplicative_reciprocalTotient
  nu_pos_of_prime := fun p hp _ => by
    change 0 < 1 / (Nat.totient p : ℝ)
    exact one_div_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp.pos)
  nu_lt_one_of_prime := fun p hp hpP => by
    change 1 / (Nat.totient p : ℝ) < 1
    have hp3 := three_le_of_prime_dvd_oddPrimorial hp hpP
    have ht : (1 : ℝ) < Nat.totient p := by
      rw [Nat.totient_prime hp]
      exact_mod_cast (show 1 < p - 1 by omega)
    exact (div_lt_one (lt_trans zero_lt_one ht)).mpr ht
  level := (z : ℝ) ^ 2
  one_le_level := by
    have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
    nlinarith

theorem prime_coprime_of_dvd_oddPrimorial (q z d : ℕ) (hq : q.Prime)
    (hzq : z < q) (hd : d ∣ oddPrimorial z) : q.Coprime d := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hqd
  exact (not_lt_of_ge ((prime_dvd_oddPrimorial_iff hq).mp (hqd.trans hd)).2) hzq

theorem middlePrimeSieve_multSum (q X z d : ℕ) (hz : 1 ≤ z)
    (hqd : q.Coprime d) :
    (middlePrimeSieve q X z hz).multSum d =
      ∑ n ∈ Ioc X (2 * X) with q * d ∣ n, vonMangoldt (n + 2) := by
  simp only [multSum, middlePrimeSieve, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hq : q ∣ n <;> by_cases hd : d ∣ n
  · simp [hq, hd, hqd.mul_dvd_of_dvd_of_dvd hq hd]
  · have h : ¬q * d ∣ n := fun h => hd (dvd_of_mul_left_dvd h)
    simp [hq, hd, h]
  · have h : ¬q * d ∣ n := fun h => hq (dvd_of_mul_right_dvd h)
    simp [hq, h]
  · have h : ¬q * d ∣ n := fun h => hq (dvd_of_mul_right_dvd h)
    simp [hq, h]

/-- No estimate for a new prime-pair correlation enters the sieve remainder. -/
theorem middlePrimeSieve_abs_rem_le (q X z d : ℕ) (hz : 1 ≤ z)
    (hq : q.Prime) (hqodd : Odd q) (hzq : z < q) (hd : d ∣ oddPrimorial z) :
    |(middlePrimeSieve q X z hz).rem d| ≤
      2 * progressionMaxError (2 * X + 2) (q * d) := by
  have hqd := prime_coprime_of_dvd_oddPrimorial q z d hq hzq hd
  have hdodd : Odd d := Nat.not_even_iff_odd.mp
    (fun h => not_two_dvd_of_dvd_oddPrimorial hd h.two_dvd)
  rw [rem, middlePrimeSieve_multSum q X z d hz hqd]
  change |(∑ n ∈ Ioc X (2 * X) with q * d ∣ n, vonMangoldt (n + 2)) -
      reciprocalTotient d * ((X : ℝ) / Nat.totient q)| ≤ _
  have hmain : reciprocalTotient d * ((X : ℝ) / Nat.totient q) =
      (X : ℝ) / Nat.totient (q * d) := by
    rw [reciprocalTotient_apply, Nat.totient_mul hqd, Nat.cast_mul]
    ring
  rw [hmain]
  exact abs_shiftedProgression_sub_main_le X (q * d) (hqodd.mul hdodd)

/-- The concrete finite upper bound retains the Selberg remainder weight.
Removing `3^ω(d)` requires a further argument and is not asserted here. -/
theorem middlePrimeSieve_siftedSum_le (q X z : ℕ) (hz : 1 ≤ z)
    (hq : q.Prime) (hqodd : Odd q) (hzq : z < q) :
    (middlePrimeSieve q X z hz).siftedSum ≤
      ((X : ℝ) / Nat.totient q) / (middlePrimeSieve q X z hz).selbergBoundingSum +
      2 * ∑ d ∈ (oddPrimorial z).divisors,
        if (d : ℝ) ≤ (z : ℝ) ^ 2 then
          (3 : ℝ) ^ ω d * progressionMaxError (2 * X + 2) (q * d) else 0 := by
  apply (SelbergSieve.selberg_bound_simple (middlePrimeSieve q X z hz)).trans
  apply add_le_add le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  change (if (d : ℝ) ≤ (z : ℝ) ^ 2 then
      (3 : ℝ) ^ ω d * |(middlePrimeSieve q X z hz).rem d| else 0) ≤ _
  split_ifs with h
  · have he := middlePrimeSieve_abs_rem_le q X z d hz hq hqodd hzq
      (Nat.dvd_of_mem_divisors hd)
    calc
      _ ≤ (3 : ℝ) ^ ω d * (2 * progressionMaxError (2 * X + 2) (q * d)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  · simp

/-- Inputs whose complete `W`-smooth part is the single prime `q`. -/
def middlePrimeInputs (q W X : ℕ) : Finset ℕ := by
  classical
  exact ((Ioc X (2 * X)).filter (q ∣ ·)).filter
    (fun n => ∀ p, p.Prime → p ∣ n / q → W < p)

/-- The positive mass whose negative is the middle-prime contribution. -/
def middlePrimeSlice (q W X : ℕ) : ℝ :=
  ∑ n ∈ middlePrimeInputs q W X, vonMangoldt (n + 2) * primeVaughanBeta W (n / q)

theorem middlePrimeSlice_nonneg (q W X : ℕ) : 0 ≤ middlePrimeSlice q W X :=
  sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (primeVaughanBeta_nonneg W (n / q))

theorem coprime_oddPrimorial_of_middlePrimeInputs (q W X z n : ℕ)
    (hq : q.Prime) (hzq : z < q) (hzW : z ≤ W)
    (hn : n ∈ middlePrimeInputs q W X) : (oddPrimorial z).Coprime n := by
  classical
  obtain ⟨hnbase, hrough⟩ := mem_filter.mp hn
  have hqn := (mem_filter.mp hnbase).2
  apply Nat.coprime_of_dvd'
  intro p hp hpP hpn
  have hpz := ((prime_dvd_oddPrimorial_iff hp).mp hpP).2
  have hpq : ¬p ∣ q := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    omega
  have hpn' : p ∣ q * (n / q) := by simpa only [Nat.mul_div_cancel' hqn] using hpn
  have hpquot := (hp.dvd_or_dvd hpn').resolve_left hpq
  exact False.elim ((not_lt_of_ge (hpz.trans hzW)) (hrough p hp hpquot))

/-- The whole beta-weighted class is bounded by the enlarged sifted set.
The quotient need not be prime, semiprime, or squarefree. -/
theorem middlePrimeSlice_le_siftedSum (q W X z : ℕ) (hz : 1 ≤ z)
    (hq : q.Prime) (hzq : z < q) (hzW : z ≤ W) (hqX : q ≤ 2 * X) :
    middlePrimeSlice q W X ≤ Real.log ((2 * X : ℝ) / q) *
      (middlePrimeSieve q X z hz).siftedSum := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hL : 0 ≤ Real.log ((2 * X : ℝ) / q) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hqpos).mpr
    simpa only [one_mul] using (show (q : ℝ) ≤ 2 * X by exact_mod_cast hqX)
  unfold middlePrimeSlice middlePrimeInputs
  rw [sum_filter]
  change _ ≤ Real.log ((2 * X : ℝ) / q) *
    ∑ n ∈ (Ioc X (2 * X)).filter (q ∣ ·),
      if (oddPrimorial z).Coprime n then vonMangoldt (n + 2) else 0
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  obtain ⟨hnI, hqn⟩ := mem_filter.mp hn
  by_cases hrough : ∀ p, p.Prime → p ∣ n / q → W < p
  · have hninput : n ∈ middlePrimeInputs q W X :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨hnI, hqn⟩, hrough⟩
    rw [if_pos hrough, if_pos (coprime_oddPrimorial_of_middlePrimeInputs
      q W X z n hq hzq hzW hninput)]
    have hnpos : 0 < n := (Nat.zero_le X).trans_lt (mem_Ioc.mp hnI).1
    have hbpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqn) hq.pos
    have hble : ((n / q : ℕ) : ℝ) ≤ (2 * X : ℝ) / q := by
      apply (le_div_iff₀ hqpos).mpr
      exact_mod_cast (show n / q * q ≤ 2 * X by
        rw [Nat.div_mul_cancel hqn]
        exact (mem_Ioc.mp hnI).2)
    have hbeta := (primeVaughanBeta_le W (n / q)).trans
      ((vaughanBeta_le_log W (n / q)).trans
        (Real.log_le_log (by exact_mod_cast hbpos) hble))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbeta
      (vonMangoldt_nonneg (n := n + 2))
  · rw [if_neg hrough]
    exact mul_nonneg hL (by split_ifs <;> positivity)

theorem middlePrimeSlice_le_selberg_bound (q W X z : ℕ) (hz : 1 ≤ z)
    (hq : q.Prime) (hqodd : Odd q) (hzq : z < q) (hzW : z ≤ W)
    (hqX : q ≤ 2 * X) :
    middlePrimeSlice q W X ≤ Real.log ((2 * X : ℝ) / q) *
      (((X : ℝ) / Nat.totient q) / (middlePrimeSieve q X z hz).selbergBoundingSum +
        2 * ∑ d ∈ (oddPrimorial z).divisors,
          if (d : ℝ) ≤ (z : ℝ) ^ 2 then
            (3 : ℝ) ^ ω d * progressionMaxError (2 * X + 2) (q * d) else 0) := by
  apply (middlePrimeSlice_le_siftedSum q W X z hz hq hzq hzW hqX).trans
  apply mul_le_mul_of_nonneg_left
    (middlePrimeSieve_siftedSum_le q X z hz hq hqodd hzq)
  apply Real.log_nonneg
  apply (le_div_iff₀ (by exact_mod_cast hq.pos : (0 : ℝ) < q)).mpr
  simpa only [one_mul] using (show (q : ℝ) ≤ 2 * X by exact_mod_cast hqX)

/-- The grouped Vaughan coefficient has exactly the claimed negative mass
on this class; this does not assert a bound for its complement. -/
theorem middlePrimeSlice_eq_neg_bilinear (U q W X : ℕ)
    (hU : 1 ≤ U) (hq : q.Prime) (hUq : U < q) (hqW : q ≤ W) :
    (∑ n ∈ middlePrimeInputs q W X,
      vonMangoldt (n + 2) * (moebiusHigh U * primeVaughanBeta W) n) =
      -middlePrimeSlice q W X := by
  classical
  rw [middlePrimeSlice, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  obtain ⟨hnbase, hrough⟩ := mem_filter.mp hn
  obtain ⟨hnI, hqn⟩ := mem_filter.mp hnbase
  have hnpos : 0 < n := (Nat.zero_le X).trans_lt (mem_Ioc.mp hnI).1
  have hbpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hnpos hqn) hq.pos
  have hcoeff := primeVaughanBilinear_eq_neg_primeBeta_of_middle_prime
    U W q (n / q) hU hq hUq hqW hbpos hrough
  rw [Nat.mul_div_cancel' hqn] at hcoeff
  rw [hcoeff]
  ring

/-- Two different primes cannot both be the complete smooth part. -/
theorem middlePrimeInputs_disjoint (q r W X : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hrW : r ≤ W) (hqr : q ≠ r) :
    Disjoint (middlePrimeInputs q W X) (middlePrimeInputs r W X) := by
  classical
  apply disjoint_left.mpr
  intro n hnq hnr
  obtain ⟨hnbase, hrough⟩ := mem_filter.mp hnq
  have hqn := (mem_filter.mp hnbase).2
  have hrn := (mem_filter.mp (mem_filter.mp hnr).1).2
  have hrn' : r ∣ q * (n / q) := by simpa only [Nat.mul_div_cancel' hqn] using hrn
  rcases hr.dvd_or_dvd hrn' with hrq | hrquot
  · exact hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrq).symm
  · exact (not_lt_of_ge hrW) (hrough r hr hrquot)

/-- The complete mass over prime smooth parts in the cutoff band. -/
def middlePrimeMass (U W X : ℕ) : ℝ :=
  ∑ q ∈ Ioc U W with q.Prime, middlePrimeSlice q W X

theorem middlePrimeMass_nonneg (U W X : ℕ) : 0 ≤ middlePrimeMass U W X :=
  sum_nonneg fun q _ => middlePrimeSlice_nonneg q W X

/-- Summing the actual finite sieve budgets controls this entire negative
class. No contribution from the complement is discarded by this theorem. -/
theorem middlePrimeMass_le_selberg_bound (U W X : ℕ) (z : ℕ → ℕ)
    (hU : 2 ≤ U) (hWX : W ≤ 2 * X)
    (hzpos : ∀ q, 1 ≤ z q)
    (hz : ∀ q ∈ Ioc U W, q.Prime → z q < q ∧ z q ≤ W) :
    middlePrimeMass U W X ≤
      ∑ q ∈ (Ioc U W).filter Nat.Prime,
        Real.log ((2 * X : ℝ) / q) *
          (((X : ℝ) / Nat.totient q) /
              (middlePrimeSieve q X (z q) (hzpos q)).selbergBoundingSum +
            2 * ∑ d ∈ (oddPrimorial (z q)).divisors,
              if (d : ℝ) ≤ (z q : ℝ) ^ 2 then
                (3 : ℝ) ^ ω d * progressionMaxError (2 * X + 2) (q * d) else 0) := by
  unfold middlePrimeMass
  apply sum_le_sum
  intro q hqmem
  obtain ⟨hqI, hq⟩ := mem_filter.mp hqmem
  obtain ⟨hzq, hzW⟩ := hz q hqI hq
  have hqodd : Odd q := hq.odd_of_ne_two (by have := (mem_Ioc.mp hqI).1; omega)
  exact middlePrimeSlice_le_selberg_bound q W X (z q) (hzpos q) hq hqodd hzq hzW
    ((mem_Ioc.mp hqI).2.trans hWX)

end TwinPrime.Analytic
