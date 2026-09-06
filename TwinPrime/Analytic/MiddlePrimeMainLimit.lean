import TwinPrime.Analytic.PrimeReciprocalLogScale
import TwinPrime.Analytic.PrimeReciprocalReplacement
import TwinPrime.Analytic.MiddlePrimePowerSieve
import TwinPrime.Analytic.MiddlePrimeSieveWeight
import TwinPrime.Analytic.MiddlePrimeReciprocalBound

/-!
# The actual middle-prime sieve main sum

The Mangoldt test-function limit is converted to a prime sum using the
proved prime-power tail. Uniform threshold rounding is summed against the
bounded reciprocal prime mass; the totient replacement is controlled
separately. All endpoints and actual sieve thresholds are retained.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Topology

namespace TwinPrime.Analytic

private theorem eventually_middlePrimeLogTest_bound
    (a v : ℝ) (hva : v < a) (ha : a < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ n ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      |middlePrimeIntegrand a (Real.log n / Real.log X) / Real.log X| ≤
        1 / ((1 / 5 : ℝ) * (a - v)) := by
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 1)
  filter_upwards [hlog, eventually_ge_atTop 2] with X hL hX n hn
  dsimp only [Function.comp_def] at hL
  obtain ⟨ht0, htv⟩ := middlePrimeLogCoordinate_bounds v X n hX hn
  have hb := abs_middlePrimeIntegrand_le a (1 / 5) v
    (middlePrimeLogCoordinate X n) (by norm_num) hva (by linarith) ⟨ht0.le, htv⟩
  have hK : 0 ≤ 1 / ((1 / 5 : ℝ) * (a - v)) := by positivity
  rw [abs_div, abs_of_pos (by linarith : 0 < Real.log X)]
  exact (div_le_div_of_nonneg_right hb (by linarith)).trans (div_le_self hK hL)

/-- The ideal prime reciprocal weight has the exact predicted limit. -/
theorem tendsto_middlePrimeIdealWeight_reciprocalSum
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    Tendsto (fun X : ℕ =>
      ∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        middlePrimeIdealWeight a X p / p) atTop
      (𝓝 (2 * ((1 / a) * Real.log (v / (1 / 5 : ℝ)) +
        ((1 - a) / a) * Real.log ((a - 1 / 5) / (a - v))))) := by
  let F : ℕ → ℕ → ℝ := fun X n =>
    middlePrimeIntegrand a (Real.log n / Real.log X) / Real.log X
  have hm := tendsto_middlePrimeIntegrand_reciprocalSum_nat
    a (1 / 5) v (by norm_num) hv.le hva (by linarith)
  change Tendsto (fun X : ℕ =>
    ∑ n ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      vonMangoldt n / n * F X n) _ _ at hm
  have hd := tendsto_sum_mangoldt_reciprocal_sub_prime primaryCutoff
    (middlePrimePowerCutoff v) F tendsto_primaryCutoff
    (1 / ((1 / 5 : ℝ) * (a - v))) (by positivity)
    (eventually_middlePrimeLogTest_bound a v hva ha)
  have hp : Tendsto (fun X : ℕ =>
      ∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        Real.log p / p * F X p) atTop
      (𝓝 ((1 / a) * Real.log (v / (1 / 5 : ℝ)) +
        ((1 - a) / a) * Real.log ((a - 1 / 5) / (a - v)))) := by
    convert hm.sub hd using 1
    · ext X
      ring
    · simp only [sub_zero]
  apply (hp.const_mul 2).congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨ht0, htv⟩ := middlePrimeLogCoordinate_bounds v X p hX hpI
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
  have hgap : a - Real.log p / Real.log X ≠ 0 := by
    change a - middlePrimeLogCoordinate X p ≠ 0
    linarith
  dsimp [F, middlePrimeIdealWeight, middlePrimeLogCoordinate, middlePrimeIntegrand]
  field_simp [hL.ne', hpLog.ne', hgap]

/-- Uniform rounding of the actual weight is negligible after summing
against the actual, bounded reciprocal prime mass. -/
theorem tendsto_middlePrimeActualWeight_sub_ideal_reciprocalSum
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    Tendsto (fun X : ℕ =>
      (∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        middlePrimeActualWeight a X p / p) -
      ∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        middlePrimeIdealWeight a X p / p) atTop (𝓝 0) := by
  obtain ⟨M, hM, hmass⟩ := eventually_sum_middlePrime_reciprocal_le v (by linarith)
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun X : ℕ =>
      (20 / ((a - v) ^ 2 * Real.log X)) * M) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.div_atTop hlog :
      Tendsto (fun X : ℕ => (20 / (a - v) ^ 2) / Real.log X) atTop (𝓝 0)).mul_const M
    simpa only [div_div, zero_mul] using h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hlim
  filter_upwards [eventually_middlePrimeActualWeight_sub_ideal_le a v hv hva ha,
    hmass, eventually_ge_atTop 2] with X hdiff hmassX hX
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hδ : 0 ≤ 20 / ((a - v) ^ 2 * Real.log X) := by positivity
  calc
    _ = |∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        (middlePrimeActualWeight a X p - middlePrimeIdealWeight a X p) / p| := by
      rw [← sum_sub_distrib]
      congr 1
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
        |(middlePrimeActualWeight a X p - middlePrimeIdealWeight a X p) / p| :=
      abs_sum_le_sum_abs _ _
    _ ≤ (20 / ((a - v) ^ 2 * Real.log X)) *
        ∑ p ∈ (Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)).filter Nat.Prime,
          (1 : ℝ) / p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      rw [abs_div, abs_of_nonneg (show 0 ≤ (p : ℝ) from Nat.cast_nonneg p)]
      exact (div_le_div_of_nonneg_right (hdiff p (mem_filter.mp hp).1)
        (Nat.cast_nonneg p)).trans_eq (by ring)
    _ ≤ (20 / ((a - v) ^ 2 * Real.log X)) * M :=
      mul_le_mul_of_nonneg_left hmassX hδ

/-- The actual sieve main sum, including totients and integer thresholds,
converges to twice the explicit rational integral. -/
theorem tendsto_middlePrimePowerMainSum
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    Tendsto (middlePrimePowerMainSum a v) atTop
      (𝓝 (2 * ((1 / a) * Real.log (v / (1 / 5 : ℝ)) +
        ((1 - a) / a) * Real.log ((a - 1 / 5) / (a - v))))) := by
  have hi := tendsto_middlePrimeIdealWeight_reciprocalSum a v hv hva ha
  have he := tendsto_middlePrimeActualWeight_sub_ideal_reciprocalSum a v hv hva ha
  have hactual := he.add hi
  simp only [sub_add_cancel, zero_add] at hactual
  have hφ := tendsto_sum_prime_totient_sub_reciprocal primaryCutoff
    (middlePrimePowerCutoff v) (middlePrimeActualWeight a) tendsto_primaryCutoff
    (1 + 2 / (a - v)) (by positivity) (by
      filter_upwards [eventually_abs_middlePrimeActualWeight_le a v hv hva ha]
        with X hX p hp _
      exact hX p hp)
  have h := hφ.add hactual
  simp only [sub_add_cancel, zero_add] at h
  convert h using 1
  ext X
  unfold middlePrimePowerMainSum
  apply sum_congr rfl
  intro p hp
  unfold middlePrimeActualWeight
  ring

end TwinPrime.Analytic
