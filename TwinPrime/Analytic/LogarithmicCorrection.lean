import TwinPrime.Analytic.MixedCorrelation
import TwinPrime.Analytic.MoebiusTotient
import TwinPrime.Analytic.PartialSummation

/-!
# The logarithmic Type I correction

The correction is reindexed by moduli before using distribution estimates.
Even moduli are bounded separately by their prime-power mass.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem truncatedMoebiusSum_eq_moduli (U n : ℕ) (hn : 0 < n) :
    truncatedMoebiusSum U n = ∑ d ∈ range (U + 1) with d ∣ n, (μ d : ℝ) := by
  unfold truncatedMoebiusSum
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_range]
  omega

theorem logarithmicCorrection_eq_progressions (U X : ℕ) :
    logarithmicCorrection U X = ∑ q ∈ range (U + 1), (μ q : ℝ) *
      ∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log ((n : ℝ) / U) * vonMangoldt (n + 2) := by
  unfold logarithmicCorrection
  simp_rw [sum_filter, mul_sum]
  calc
    _ = ∑ n ∈ Ioc X (2 * X), ∑ q ∈ range (U + 1),
        if q ∣ n then (μ q : ℝ) * Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)
          else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [truncatedMoebiusSum_eq_moduli U n (by have := (mem_Ioc.mp hn).1; omega),
        sum_filter, mul_sum, mul_sum]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp [mul_assoc, mul_comm]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp [mul_assoc]

theorem log_ratio_nonneg {U X n : ℕ} (hU : 0 < U) (hUX : U ≤ X)
    (hn : n ∈ Ioc X (2 * X)) : 0 ≤ Real.log ((n : ℝ) / U) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by exact_mod_cast hU : (0 : ℝ) < U)]
  simp only [one_mul]
  exact_mod_cast (show U ≤ n by have := mem_Ioc.mp hn; omega)

theorem log_ratio_le_dyadic {U X n : ℕ} (hU : 0 < U)
    (hn : n ∈ Ioc X (2 * X)) :
    Real.log ((n : ℝ) / U) ≤ Real.log (2 * X + 2) := by
  have hUp : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := mem_Ioc.mp hn; omega)
  apply Real.log_le_log (div_pos hnp hUp)
  apply (div_le_self (le_of_lt hnp) hU1).trans
  exact_mod_cast (show n ≤ 2 * X + 2 by have := mem_Ioc.mp hn; omega)

theorem even_logarithmicProgression_le (U X q : ℕ) (hU : 0 < U) (hUX : U ≤ X)
    (hq : Even q) :
    |∑ n ∈ Ioc X (2 * X) with q ∣ n,
      Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)| ≤
        Real.log (2 * X + 2) * evenProgressionBound X := by
  rw [abs_of_nonneg (sum_nonneg (fun n hn => mul_nonneg
    (log_ratio_nonneg hU hUX (mem_filter.mp hn).1) vonMangoldt_nonneg))]
  calc
    _ ≤ ∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log (2 * X + 2) * vonMangoldt (n + 2) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (log_ratio_le_dyadic hU (mem_filter.mp hn).1)
        vonMangoldt_nonneg
    _ = Real.log (2 * X + 2) *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (even_shiftedProgression_le X q hq)
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith))

/-- Cumulative shifted errors on every intermediate integer endpoint. -/
theorem shiftedProgression_interval_sub_main_eq_errors (a b q : ℕ) (hab : a ≤ b) :
    (∑ n ∈ Ioc a b with q ∣ n, vonMangoldt (n + 2)) -
      ((b : ℝ) - a) / Nat.totient q =
        progressionError (b + 2) q 2 - progressionError (a + 2) q 2 := by
  have hs : (∑ n ∈ Ioc a b with q ∣ n, vonMangoldt (n + 2)) =
      progressionPsi (b + 2) q 2 - progressionPsi (a + 2) q 2 := by
    rw [progressionPsi_sub _ _ _ _ (by omega)]
    apply sum_bij (fun n _ => n + 2)
    · intro n hn
      obtain ⟨hnI, hqn⟩ := mem_filter.mp hn
      apply mem_filter.mpr
      refine ⟨?_, Nat.add_modEq_right_iff.mpr hqn⟩
      simp only [mem_Ioc] at hnI ⊢
      omega
    · intro n _ m _ h
      omega
    · intro m hm
      obtain ⟨hmI, hmcong⟩ := mem_filter.mp hm
      have hm := mem_Ioc.mp hmI
      have heq : m - 2 + 2 = m := by omega
      refine ⟨m - 2, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩, heq⟩
      have hcong : Nat.ModEq q (m - 2 + 2) 2 := by simpa only [heq] using hmcong
      exact Nat.add_modEq_right_iff.mp hcong
    · intro n _
      rfl
  rw [hs]
  unfold progressionError
  push_cast
  ring

/-- The unweighted integer main mass arising in partial summation. -/
def logarithmicMass (U X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X), Real.log ((n : ℝ) / U)

theorem logarithmicMass_nonneg (U X : ℕ) (hU : 0 < U) (hUX : U ≤ X) :
    0 ≤ logarithmicMass U X :=
  sum_nonneg (fun _ hn => log_ratio_nonneg hU hUX hn)

theorem logarithmicMass_le (U X : ℕ) (hU : 0 < U) :
    logarithmicMass U X ≤ X * Real.log (2 * X + 2) := by
  calc
    _ ≤ ∑ n ∈ Ioc X (2 * X), Real.log (2 * X + 2) :=
      sum_le_sum (fun _ hn => log_ratio_le_dyadic hU hn)
    _ = _ := by simp [Nat.card_Ioc, show 2 * X - X = X by omega]

theorem oddCutoff_eq_range_filter (U : ℕ) :
    oddCutoff U = (range (U + 1)).filter Odd := by
  ext q
  simp only [oddCutoff, mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, hq⟩, ho⟩
    exact ⟨by omega, ho⟩
  · rintro ⟨hq, ho⟩
    exact ⟨⟨ho.pos, by omega⟩, ho⟩

/-- A finite assembly lemma retaining a separate reduced-residue estimate. -/
theorem logarithmicCorrection_error_le_of_progressions (U X : ℕ)
    (hU : 0 < U) (hUX : U ≤ X)
    (hodd : ∀ q, Odd q →
      |(∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)) -
          logarithmicMass U X / Nat.totient q| ≤
            4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q) :
    |logarithmicCorrection U X - oddMoebiusTotientSum U * logarithmicMass U X| ≤
      4 * Real.log (2 * X + 2) * ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q +
        (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X := by
  let f := fun q => ∑ n ∈ Ioc X (2 * X) with q ∣ n,
    Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)
  have hL : 0 ≤ Real.log (2 * X + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hmu (q : ℕ) : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := q))
  have hdecomp : logarithmicCorrection U X =
      (∑ q ∈ oddCutoff U, (μ q : ℝ) * f q) +
        ∑ q ∈ range (U + 1) with Even q, (μ q : ℝ) * f q := by
    rw [logarithmicCorrection_eq_progressions, oddCutoff_eq_range_filter]
    simpa only [Nat.not_odd_iff_even] using
      (sum_filter_add_sum_filter_not (range (U + 1)) Odd (fun q => (μ q : ℝ) * f q)).symm
  have ho : |(∑ q ∈ oddCutoff U, (μ q : ℝ) * f q) -
      oddMoebiusTotientSum U * logarithmicMass U X| ≤
        4 * Real.log (2 * X + 2) * ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q := by
    unfold oddMoebiusTotientSum
    rw [sum_mul, ← sum_sub_distrib]
    calc
      _ ≤ ∑ q ∈ oddCutoff U, |(μ q : ℝ) * f q -
          (μ q : ℝ) / Nat.totient q * logarithmicMass U X| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ oddCutoff U, 4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q := by
        apply sum_le_sum
        intro q hq
        have heq : (μ q : ℝ) * f q - (μ q : ℝ) / Nat.totient q * logarithmicMass U X =
            (μ q : ℝ) * (f q - logarithmicMass U X / Nat.totient q) := by ring
        rw [heq, abs_mul]
        calc
          _ ≤ 1 * |f q - logarithmicMass U X / Nat.totient q| :=
            mul_le_mul_of_nonneg_right (hmu q) (abs_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using hodd q (mem_filter.mp hq).2
      _ ≤ ∑ q ∈ Icc 1 U, 4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ =>
          mul_nonneg (by positivity) (progressionMaxError_nonneg _ q))
      _ = _ := (mul_sum ..).symm
  have he : |∑ q ∈ range (U + 1) with Even q, (μ q : ℝ) * f q| ≤
      (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X := by
    calc
      _ ≤ ∑ q ∈ range (U + 1) with Even q, |(μ q : ℝ) * f q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ range (U + 1) with Even q,
          Real.log (2 * X + 2) * evenProgressionBound X := by
        apply sum_le_sum
        intro q hq
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hmu q) (abs_nonneg _)).trans
          (by simpa only [one_mul] using
            (even_logarithmicProgression_le U X q hU hUX (mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ range (U + 1), Real.log (2 * X + 2) * evenProgressionBound X :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ =>
          mul_nonneg hL (evenProgressionBound_nonneg X))
      _ = _ := by simp; ring
  rw [hdecomp, add_sub_right_comm]
  exact (abs_add_le _ _).trans (add_le_add ho he)

/-- Partial summation controls each logarithmically weighted reduced residue. -/
theorem odd_logarithmicProgression_error_le (U X q : ℕ) (hU : 0 < U) (hUX : U ≤ X)
    (hq : Odd q) :
    |(∑ n ∈ Ioc X (2 * X) with q ∣ n,
      Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)) -
        logarithmicMass U X / Nat.totient q| ≤
          4 * Real.log (2 * X + 2) * progressionMaxError (2 * X + 2) q := by
  let e := fun n => (if q ∣ n then vonMangoldt (n + 2) else 0) - (1 : ℝ) / Nat.totient q
  have hE : ∀ t ∈ Icc X (2 * X), |∑ n ∈ Ioc X t, e n| ≤
      2 * progressionMaxError (2 * X + 2) q := by
    intro t ht
    obtain ⟨hXt, htX⟩ := mem_Icc.mp ht
    have heq : (∑ n ∈ Ioc X t, e n) =
        (∑ n ∈ Ioc X t with q ∣ n, vonMangoldt (n + 2)) -
          ((t : ℝ) - X) / Nat.totient q := by
      simp [e, sum_sub_distrib, sum_filter, Nat.card_Ioc, Nat.cast_sub hXt, div_eq_mul_inv]
    rw [heq, shiftedProgression_interval_sub_main_eq_errors X t q hXt]
    calc
      _ ≤ |progressionError (t + 2) q 2| + |progressionError (X + 2) q 2| := abs_sub _ _
      _ ≤ progressionMaxError (2 * X + 2) q + progressionMaxError (2 * X + 2) q :=
        add_le_add (abs_progressionError_two_le_max (by omega) hq)
          (abs_progressionError_two_le_max (by omega) hq)
      _ = _ := by ring
  have h := abs_sum_Ioc_log_mul_le_of_partial_sums X (2 * X) U (by omega) hU hUX e
    (2 * progressionMaxError (2 * X + 2) q)
    (mul_nonneg (by norm_num) (progressionMaxError_nonneg _ q)) hE
  have heq : (∑ n ∈ Ioc X (2 * X), Real.log ((n : ℝ) / U) * e n) =
      (∑ n ∈ Ioc X (2 * X) with q ∣ n,
        Real.log ((n : ℝ) / U) * vonMangoldt (n + 2)) -
          logarithmicMass U X / Nat.totient q := by
    simp only [e, mul_sub, sum_sub_distrib, sum_filter, logarithmicMass, sum_div]
    congr 1
    · apply sum_congr rfl
      intro n _
      split_ifs <;> simp
    · apply sum_congr rfl
      intro n _
      ring
  rw [heq] at h
  have hX : 0 < X := hU.trans_le hUX
  have hl := log_ratio_le_dyadic hU
    (mem_Ioc.mpr (show X < 2 * X ∧ 2 * X ≤ 2 * X by omega))
  have hh := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 2 * (2 * progressionMaxError (2 * X + 2) q) by
      have := progressionMaxError_nonneg (2 * X + 2) q; positivity)
  exact h.trans (by convert hh using 1; ring)

theorem logarithmicCorrection_error_le (U X : ℕ) (hU : 0 < U) (hUX : U ≤ X) :
    |logarithmicCorrection U X - oddMoebiusTotientSum U * logarithmicMass U X| ≤
      4 * Real.log (2 * X + 2) * ∑ q ∈ Icc 1 U, progressionMaxError (2 * X + 2) q +
        (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X :=
  logarithmicCorrection_error_le_of_progressions U X hU hUX
    (fun q hq => odd_logarithmicProgression_error_le U X q hU hUX hq)

theorem logarithmicCorrection_error_le_primary (X : ℕ) (hX : 1 ≤ X) :
    |logarithmicCorrection (primaryCutoff X) X -
      oddMoebiusTotientSum (primaryCutoff X) * logarithmicMass (primaryCutoff X) X| ≤
        4 * Real.log (2 * X + 2) * primaryProgressionError X + evenWeightBudget X := by
  let U := primaryCutoff X
  have hU : 1 ≤ U := primaryCutoff_pos hX
  have hUsq : U ≤ U ^ 2 := by nlinarith
  have hL : 0 ≤ Real.log (2 * X + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  apply (logarithmicCorrection_error_le U X hU (primaryCutoff_le hX)).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sum_progressionMaxError_le_primary hUsq) (by positivity)
  · change (U + 1 : ℝ) * Real.log (2 * X + 2) * evenProgressionBound X ≤
      ((U : ℝ) ^ 2 + 1) * Real.log (2 * X + 2) * evenProgressionBound X
    apply mul_le_mul_of_nonneg_right _ (evenProgressionBound_nonneg X)
    apply mul_le_mul_of_nonneg_right _ hL
    exact_mod_cast (show U + 1 ≤ U ^ 2 + 1 by omega)

theorem MaximalBombieriVinogradov.tendsto_logarithmic_error_div (hBV : MaximalBombieriVinogradov) :
    Tendsto (fun X : ℕ => (logarithmicCorrection (primaryCutoff X) X -
      oddMoebiusTotientSum (primaryCutoff X) * logarithmicMass (primaryCutoff X) X) / X)
        atTop (nhds 0) := by
  have h := (hBV.tendsto_log_mul_sum_error_div.const_mul 4).add tendsto_evenWeightBudget_div
  simp only [mul_zero, zero_add] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with X hX
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)]
    have hb := div_le_div_of_nonneg_right (logarithmicCorrection_error_le_primary X hX)
      (Nat.cast_nonneg (α := ℝ) X)
    simpa only [add_div, mul_div_assoc, mul_assoc] using hb

theorem tendsto_logarithmicCorrection_div_of_inputs (hBV : MaximalBombieriVinogradov)
    (hF : Tendsto (fun X : ℕ => oddMoebiusTotientSum (primaryCutoff X) * Real.log (2 * X + 2))
      atTop (nhds 0)) :
    Tendsto (fun X : ℕ => logarithmicCorrection (primaryCutoff X) X / X) atTop (nhds 0) := by
  have hmain : Tendsto (fun X : ℕ =>
      oddMoebiusTotientSum (primaryCutoff X) * logarithmicMass (primaryCutoff X) X / X)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hFabs := hF.abs
    simp only [abs_zero] at hFabs
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hFabs
    · filter_upwards with X
      exact abs_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with X hX
      have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
      have hL : 0 ≤ Real.log (2 * X + 2) :=
        Real.log_nonneg (by have := hx.le; linarith)
      dsimp only [Function.comp_def]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hx,
        abs_of_nonneg (logarithmicMass_nonneg _ _ (primaryCutoff_pos hX) (primaryCutoff_le hX)),
        abs_of_nonneg hL]
      rw [div_le_iff₀ hx]
      have hh := mul_le_mul_of_nonneg_left
        (logarithmicMass_le (primaryCutoff X) X (primaryCutoff_pos hX))
        (abs_nonneg (oddMoebiusTotientSum (primaryCutoff X)))
      nlinarith
  have h := hBV.tendsto_logarithmic_error_div.add hmain
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards with X
  rw [← add_div]
  congr 1
  ring

end TwinPrime.Analytic
