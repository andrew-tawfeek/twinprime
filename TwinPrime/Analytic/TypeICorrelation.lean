import TwinPrime.Analytic.PrimeDistribution
import TwinPrime.Analytic.GrowthBounds
import TwinPrime.Analytic.EvenAsymptotics
import TwinPrime.Analytic.MoebiusTotient

/-!
# The Type I correlation and its classical inputs

Finite reindexing identifies the odd-modulus main coefficient with the exact
two-factor sum `totientTypeIMain`, including its shared-prime correction.
The finite error separates odd progression errors and even-modulus exceptions.
The limiting results retain Bombieri–Vinogradov and main-coefficient decay as
separate explicit hypotheses.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- The convolution main coefficient is exactly the two-factor totient sum.
No multiplicativity of the totient at noncoprime factors is used. -/
theorem vaughanCoefficient_odd_totient_sum_eq (U V : ℕ) :
    (∑ q ∈ range (U * V + 1) with Odd q,
      vaughanCoefficient U V q / Nat.totient q) = totientTypeIMain U V := by
  have hexpand :
      (∑ q ∈ range (U * V + 1) with Odd q,
        vaughanCoefficient U V q / Nat.totient q) =
      ∑ q ∈ range (U * V + 1) with Odd q,
        ∑ db ∈ q.divisorsAntidiagonal with db.1 ≤ U ∧ db.2 ≤ V,
          (μ db.1 : ℝ) * vonMangoldt db.2 / Nat.totient q := by
    apply sum_congr rfl
    intro q _
    rw [vaughanCoefficient_apply, sum_div, sum_filter]
    apply sum_congr rfl
    intro db _
    split_ifs <;> simp
  rw [hexpand, sum_sigma']
  unfold totientTypeIMain
  rw [← sum_product' (oddCutoff U) (oddCutoff V)
    (fun d b => (μ d : ℝ) * vonMangoldt b / Nat.totient (d * b))]
  apply sum_bij (fun qdb _ => qdb.2)
  · rintro ⟨q, db⟩ hqdb
    obtain ⟨hq, hdb⟩ := mem_sigma.mp hqdb
    obtain ⟨hanti, hdU, hbV⟩ := mem_filter.mp hdb
    have hprod : db.1 * db.2 = q := (Nat.mem_divisorsAntidiagonal.mp hanti).1
    have hodd : Odd (db.1 * db.2) := by rw [hprod]; exact (mem_filter.mp hq).2
    apply mem_product.mpr
    constructor
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero
        (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hanti), hdU⟩,
        Nat.Odd.of_mul_left hodd⟩
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero
        (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hanti), hbV⟩,
        Nat.Odd.of_mul_right hodd⟩
  · rintro ⟨q, db⟩ hqdb ⟨r, ec⟩ hrec heq
    dsimp only at heq
    subst ec
    have hq := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hqdb).2).1).1
    have hr := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hrec).2).1).1
    have hqr : q = r := hq.symm.trans hr
    subst r
    rfl
  · intro db hdb
    obtain ⟨hd, hb⟩ := mem_product.mp hdb
    obtain ⟨hdI, hdodd⟩ := mem_filter.mp hd
    obtain ⟨hbI, hbodd⟩ := mem_filter.mp hb
    have hdU := mem_Icc.mp hdI
    have hbV := mem_Icc.mp hbI
    have hprod := Nat.mul_le_mul hdU.2 hbV.2
    refine ⟨⟨db.1 * db.2, db⟩, mem_sigma.mpr ⟨?_, ?_⟩, rfl⟩
    · exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hprod), hdodd.mul hbodd⟩
    · exact mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
        ⟨rfl, (Nat.mul_pos hdU.1 hbV.1).ne'⟩, hdU.2, hbV.2⟩
  · rintro ⟨q, db⟩ hqdb
    have hprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hqdb).2).1).1
    dsimp only
    rw [hprod]

theorem typeITerm_eq_odd_add_even (U V X : ℕ) :
    typeITerm U V X =
      (∑ q ∈ range (U * V + 1) with Odd q, vaughanCoefficient U V q *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)) +
      ∑ q ∈ range (U * V + 1) with Even q, vaughanCoefficient U V q *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2) := by
  rw [typeITerm_eq_progressions]
  simpa only [Nat.not_odd_iff_even] using
    (sum_filter_add_sum_filter_not (range (U * V + 1)) Odd
      (fun q => vaughanCoefficient U V q *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2))).symm

theorem abs_vaughanCoefficient_le_log_cutoff (U V q : ℕ) (hq : q ≤ U * V) :
    |vaughanCoefficient U V q| ≤ Real.log (U * V + 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [ArithmeticFunction.map_zero, abs_zero]
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) (U * V)
    push_cast at this
    linarith
  · apply (abs_vaughanCoefficient_le_log U V q).trans
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq0)
    exact_mod_cast (show q ≤ U * V + 1 by omega)

/-- Finite Type I error with explicit odd and even modulus contributions. -/
theorem typeICorrelation_error_le (U V X : ℕ) :
    |typeITerm U V X - (X : ℝ) * totientTypeIMain U V| ≤
      2 * Real.log (U * V + 1) *
        ∑ q ∈ Icc 1 (U * V), progressionMaxError (2 * X + 2) q +
      (U * V + 1 : ℝ) * Real.log (U * V + 1) * evenProgressionBound X := by
  have hL : 0 ≤ Real.log (U * V + 1) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) (U * V)
    push_cast at this
    linarith
  have hodd := weighted_odd_progression_error_le_of_cap (U * V) X
    (vaughanCoefficient U V) (Real.log (U * V + 1)) hL
    (fun q hq _ => abs_vaughanCoefficient_le_log_cutoff U V q (mem_Icc.mp hq).2)
  have heven := weighted_even_progression_le X ((range (U * V + 1)).filter Even)
    (vaughanCoefficient U V) (fun q hq => (mem_filter.mp hq).2)
  have hnorm : (∑ q ∈ range (U * V + 1) with Even q, |vaughanCoefficient U V q|) ≤
      (U * V + 1 : ℝ) * Real.log (U * V + 1) := by
    calc
      _ ≤ ∑ q ∈ range (U * V + 1) with Even q, Real.log (U * V + 1) := by
        apply sum_le_sum
        intro q hq
        exact abs_vaughanCoefficient_le_log_cutoff U V q
          (by have := mem_range.mp (mem_filter.mp hq).1; omega)
      _ ≤ ∑ q ∈ range (U * V + 1), Real.log (U * V + 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hL)
      _ = _ := by simp
  have heven' := heven.trans (mul_le_mul_of_nonneg_right hnorm (evenProgressionBound_nonneg X))
  rw [vaughanCoefficient_odd_totient_sum_eq] at hodd
  rw [typeITerm_eq_odd_add_even]
  have htriangle := abs_add_le
    ((∑ q ∈ range (U * V + 1) with Odd q, vaughanCoefficient U V q *
      ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)) -
        (X : ℝ) * totientTypeIMain U V)
    (∑ q ∈ range (U * V + 1) with Even q, vaughanCoefficient U V q *
      ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2))
  rw [sub_add_eq_add_sub] at htriangle
  exact htriangle.trans (add_le_add hodd heven')

theorem typeICorrelation_error_le_primary (X : ℕ) (hX : 1 ≤ X) :
    |typeITerm (primaryCutoff X) (primaryCutoff X) X -
      (X : ℝ) * totientTypeIMain (primaryCutoff X) (primaryCutoff X)| ≤
      2 * Real.log (2 * X + 2) * primaryProgressionError X + evenWeightBudget X := by
  let U := primaryCutoff X
  have hUsqX : U ^ 2 ≤ X := by
    have h := (primaryCutoff_sq_le_rpow X).trans
      (Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by norm_num : (2 / 5 : ℝ) ≤ 1))
    exact_mod_cast h
  have hL : 0 ≤ Real.log (U * U + 1) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) (U * U)
    push_cast at this
    linarith
  have hLog : Real.log (U * U + 1) ≤ Real.log (2 * X + 2) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show U * U + 1 ≤ 2 * X + 2 by nlinarith)
  apply (typeICorrelation_error_le U U X).trans
  apply add_le_add
  · apply mul_le_mul (mul_le_mul_of_nonneg_left hLog (by norm_num))
      (sum_progressionMaxError_le_primary (by dsimp [U]; nlinarith))
    · exact sum_nonneg (fun q _ => progressionMaxError_nonneg _ q)
    · have := hL.trans hLog
      positivity
  · change (U * U + 1 : ℝ) * Real.log (U * U + 1) * evenProgressionBound X ≤
      ((U : ℝ) ^ 2 + 1) * Real.log (2 * X + 2) * evenProgressionBound X
    apply mul_le_mul_of_nonneg_right _ (evenProgressionBound_nonneg X)
    apply mul_le_mul _ hLog hL (by positivity)
    nlinarith

/-- The Type I remainder is sublinear under the explicit distribution input. -/
theorem MaximalBombieriVinogradov.tendsto_typeI_error_div (hBV : MaximalBombieriVinogradov) :
    Tendsto (fun X : ℕ => (typeITerm (primaryCutoff X) (primaryCutoff X) X -
      (X : ℝ) * totientTypeIMain (primaryCutoff X) (primaryCutoff X)) / X)
      atTop (nhds 0) := by
  have h := (hBV.tendsto_log_mul_sum_error_div.const_mul 2).add tendsto_evenWeightBudget_div
  simp only [mul_zero, zero_add] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with X hX
    dsimp only [Function.comp_def]
    rw [abs_div]
    rw [show |(X : ℝ)| = (X : ℝ) from abs_of_nonneg (Nat.cast_nonneg X)]
    have hb := div_le_div_of_nonneg_right (typeICorrelation_error_le_primary X hX)
      (Nat.cast_nonneg (α := ℝ) X)
    simpa only [add_div, mul_div_assoc, mul_assoc] using hb

theorem MaximalBombieriVinogradov.tendsto_typeI_div_sub_main (hBV : MaximalBombieriVinogradov) :
    Tendsto (fun X : ℕ => typeITerm (primaryCutoff X) (primaryCutoff X) X / X -
      totientTypeIMain (primaryCutoff X) (primaryCutoff X)) atTop (nhds 0) := by
  apply hBV.tendsto_typeI_error_div.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  field_simp

/-- Main-coefficient decay is a separate classical input, not a consequence of BV. -/
theorem tendsto_typeITerm_div_of_inputs (hBV : MaximalBombieriVinogradov)
    (hQ : Tendsto (fun X : ℕ => totientTypeIMain (primaryCutoff X) (primaryCutoff X))
      atTop (nhds 0)) :
    Tendsto (fun X : ℕ => typeITerm (primaryCutoff X) (primaryCutoff X) X / X)
      atTop (nhds 0) := by
  have h := hBV.tendsto_typeI_div_sub_main.add hQ
  simpa only [zero_add, sub_add_cancel] using h

end TwinPrime.Analytic
