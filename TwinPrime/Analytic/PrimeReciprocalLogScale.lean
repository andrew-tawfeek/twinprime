import TwinPrime.Analytic.PrimeReciprocalAbel
import TwinPrime.Analytic.ClassicalDistribution
import TwinPrime.Analytic.MiddlePrimeIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmically scaled reciprocal Mangoldt sums

The finite centered Abel bound is applied to an actual continuously
differentiable test function. The reciprocal Mangoldt input is discharged
by the repository's unconditional classical distribution theorem.
-/

noncomputable section

open Finset MeasureTheory ArithmeticFunction Filter
open scoped Topology

namespace TwinPrime.Analytic

def logScaleTestFunction (g : ℝ → ℝ) (L y : ℝ) : ℝ :=
  g (Real.log y / L) / L

private theorem logScale_mem {L u v y : ℝ} (hL : 0 < L) (_huv : u ≤ v)
    (hy : y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) :
    Real.log y / L ∈ Set.Icc u v := by
  have hy0 := (Real.exp_pos (u * L)).trans_le hy.1
  constructor
  · apply (le_div_iff₀ hL).mpr
    simpa using Real.log_le_log (Real.exp_pos (u * L)) hy.1
  · apply (div_le_iff₀ hL).mpr
    simpa using Real.log_le_log hy0 hy.2

private theorem hasDerivAt_logScaleTestFunction
    {g : ℝ → ℝ} {L y : ℝ} (hL : L ≠ 0) (hy : 0 < y)
    (hg : DifferentiableAt ℝ g (Real.log y / L)) :
    HasDerivAt (logScaleTestFunction g L)
      (deriv g (Real.log y / L) / L ^ 2 / y) y := by
  have h := (hg.hasDerivAt.comp y ((Real.hasDerivAt_log hy.ne').div_const L)).div_const L
  have heq : deriv g (Real.log y / L) / L ^ 2 / y =
      (deriv g (Real.log y / L) * (y⁻¹ / L)) / L := by
    field_simp
  rw [heq]
  exact h

private theorem continuousOn_logScaleDerivative
    {g : ℝ → ℝ} {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg : ContinuousOn (deriv g) (Set.Icc u v)) :
    ContinuousOn (fun y => deriv g (Real.log y / L) / L ^ 2 / y)
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) := by
  have hypos : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)), 0 < y :=
    fun y hy => (Real.exp_pos (u * L)).trans_le hy.1
  have hc : ContinuousOn (fun y => Real.log y / L)
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) := by
    have hlog : ContinuousOn Real.log
        (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) :=
      fun y hy => (Real.continuousAt_log (hypos y hy).ne').continuousWithinAt
    exact hlog.div_const L
  exact ((hg.comp hc (fun y hy => logScale_mem hL huv hy)).div_const _).div
    continuousOn_id (fun y hy => (hypos y hy).ne')

theorem integral_logScaleTestFunction_div
    {g : ℝ → ℝ} {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg : ContinuousOn g (Set.Icc u v)) :
    (∫ y in Real.exp (u * L)..Real.exp (v * L), logScaleTestFunction g L y / y) =
      ∫ t in u..v, g t := by
  have hab : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hL.le)
  have hder : ∀ y ∈ Set.uIcc (Real.exp (u * L)) (Real.exp (v * L)),
      HasDerivAt (fun y => Real.log y / L) (1 / y / L) y := by
    intro y hy
    have hy0 : 0 < y := (Real.exp_pos (u * L)).trans_le ((Set.uIcc_of_le hab ▸ hy).1)
    simpa only [one_div] using (Real.hasDerivAt_log hy0.ne').div_const L
  have hc : ContinuousOn (fun y : ℝ => 1 / y / L)
      (Set.uIcc (Real.exp (u * L)) (Real.exp (v * L))) := by
    apply ContinuousOn.div_const
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact ((Real.exp_pos (u * L)).trans_le ((Set.uIcc_of_le hab ▸ hy).1)).ne'
  have hgimage : ContinuousOn g ((fun y => Real.log y / L) ''
      Set.uIcc (Real.exp (u * L)) (Real.exp (v * L))) := by
    apply hg.mono
    rintro t ⟨y, hy, rfl⟩
    exact logScale_mem hL huv (Set.uIcc_of_le hab ▸ hy)
  have h := intervalIntegral.integral_comp_mul_deriv' hder hc hgimage
  simp only [Real.log_exp, mul_div_cancel_right₀ _ hL.ne'] at h
  convert h using 1
  congr 1
  ext y
  simp only [Function.comp_apply, logScaleTestFunction]
  ring

theorem abs_logScaleTestFunction_variation_le
    {g : ℝ → ℝ} {L u v K : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v))
    (hK : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K) :
    (∫ y in Real.exp (u * L)..Real.exp (v * L),
      |deriv (logScaleTestFunction g L) y|) ≤ K * (v - u) / L := by
  have hab : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hL.le)
  have hformula : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
      deriv (logScaleTestFunction g L) y = deriv g (Real.log y / L) / L ^ 2 / y := by
    intro y hy
    exact (hasDerivAt_logScaleTestFunction hL.ne'
      ((Real.exp_pos (u * L)).trans_le hy.1) (hg_diff _ (logScale_mem hL huv hy))).deriv
  have hc := continuousOn_logScaleDerivative hL huv hg_deriv
  have hfcont : ContinuousOn (deriv (logScaleTestFunction g L))
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) := hc.congr hformula
  have hInv : ContinuousOn (fun y : ℝ => 1 / y)
      (Set.uIcc (Real.exp (u * L)) (Real.exp (v * L))) := by
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact ((Real.exp_pos (u * L)).trans_le ((Set.uIcc_of_le hab ▸ hy).1)).ne'
  have hmain : (∫ y in Real.exp (u * L)..Real.exp (v * L), 1 / y) = (v - u) * L := by
    rw [integral_one_div (by
      rw [Set.uIcc_of_le hab]
      exact fun h => (not_le_of_gt (Real.exp_pos (u * L))) h.1)]
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  calc
    _ ≤ ∫ y in Real.exp (u * L)..Real.exp (v * L), (K / L ^ 2) * (1 / y) := by
      apply intervalIntegral.integral_mono_on hab
        ((Set.uIcc_of_le hab).symm ▸ hfcont.abs).intervalIntegrable
        (hInv.const_mul _).intervalIntegrable
      intro y hy
      have hy0 := (Real.exp_pos (u * L)).trans_le hy.1
      rw [hformula y hy, abs_div, abs_div, abs_of_pos (sq_pos_of_pos hL), abs_of_pos hy0]
      exact (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hK _ (logScale_mem hL huv hy)) (sq_nonneg L)) hy0.le).trans_eq (by ring)
    _ = K * (v - u) / L := by
      rw [intervalIntegral.integral_const_mul, hmain]
      field_simp

/-- Finite, exact-floor version of centered Abel summation for a logarithmic
test function. Both signs of the derivative are allowed. -/
theorem abs_logScale_primeReciprocal_error_le
    {g : ℝ → ℝ} {L u v : ℝ} (hL : 0 < L) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v)) (K₀ K₁ c M : ℝ)
    (hK₀ : ∀ t ∈ Set.Icc u v, |g t| ≤ K₀)
    (hK₁ : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K₁)
    (herror : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
      |realPrimeReciprocalSum y - Real.log y - c| ≤ M) :
    |(∑ n ∈ Ioc ⌊Real.exp (u * L)⌋₊ ⌊Real.exp (v * L)⌋₊,
        vonMangoldt n / (n : ℝ) * (g (Real.log n / L) / L)) -
          (∫ t in u..v, g t)| ≤ M * (2 * K₀ + K₁ * (v - u)) / L := by
  have hab : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hL.le)
  have hdf : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
      HasDerivAt (logScaleTestFunction g L)
        (deriv g (Real.log y / L) / L ^ 2 / y) y := by
    intro y hy
    exact hasDerivAt_logScaleTestFunction hL.ne'
      ((Real.exp_pos (u * L)).trans_le hy.1) (hg_diff _ (logScale_mem hL huv hy))
  have hfcont : ContinuousOn (deriv (logScaleTestFunction g L))
      (Set.Icc (Real.exp (u * L)) (Real.exp (v * L))) :=
    (continuousOn_logScaleDerivative hL huv hg_deriv).congr (fun y hy => (hdf y hy).deriv)
  have hgcont : ContinuousOn g (Set.Icc u v) :=
    fun t ht => (hg_diff t ht).continuousAt.continuousWithinAt
  have h := abs_primeReciprocal_abel_error_le_of_continuous_deriv
    (Real.exp_pos (u * L)) hab (fun y hy => (hdf y hy).differentiableAt)
    hfcont c M herror
  rw [integral_logScaleTestFunction_div hL huv hgcont] at h
  have hM : 0 ≤ M := (abs_nonneg _).trans (herror _ ⟨le_rfl, hab⟩)
  have hend (t : ℝ) (ht : t ∈ Set.Icc u v) :
      |logScaleTestFunction g L (Real.exp (t * L))| ≤ K₀ / L := by
    simp only [logScaleTestFunction, Real.log_exp, mul_div_cancel_right₀ _ hL.ne',
      abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (hK₀ t ht) hL.le
  exact h.trans <| (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (hend u ⟨le_rfl, huv⟩) (hend v ⟨huv, le_rfl⟩))
      (abs_logScaleTestFunction_variation_le hL huv hg_diff hg_deriv hK₁)) hM).trans_eq (by ring)

/-- The actual reciprocal Mangoldt sum on a fixed logarithmic window. -/
def logScalePrimeReciprocalSum (g : ℝ → ℝ) (u v x : ℝ) : ℝ :=
  ∑ n ∈ Ioc ⌊x ^ u⌋₊ ⌊x ^ v⌋₊,
    vonMangoldt n / (n : ℝ) * (g (Real.log n / Real.log x) / Real.log x)

/-- Unconditional quantitative summation of a fixed test function on a
logarithmic window. The constants bounding the function and its derivative
are finite regularity data, not prime-distribution assumptions. -/
theorem exists_logScalePrimeReciprocalSum_error_bound
    (g : ℝ → ℝ) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v)) (K₀ K₁ : ℝ)
    (hK₀ : ∀ t ∈ Set.Icc u v, |g t| ≤ K₀)
    (hK₁ : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K₁) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℝ in atTop,
      |logScalePrimeReciprocalSum g u v x - ∫ t in u..v, g t| ≤
        B / (Real.log x) ^ 6 := by
  obtain ⟨c, C, hC, hcenter⟩ := maximal_bombieri_vinogradov.real_primeReciprocal_center
  obtain ⟨y₀, hy₀⟩ := (eventually_atTop.1 hcenter)
  have hK₀pos : 0 ≤ K₀ := (abs_nonneg _).trans (hK₀ u ⟨le_rfl, huv⟩)
  have hK₁pos : 0 ≤ K₁ := (abs_nonneg _).trans (hK₁ u ⟨le_rfl, huv⟩)
  let B : ℝ := C * (2 * K₀ + K₁ * (v - u)) / u ^ 5
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg hC (add_nonneg (by positivity)
      (mul_nonneg hK₁pos (sub_nonneg.mpr huv)))) (pow_pos hu _).le
  have hLower : Tendsto (fun L : ℝ => Real.exp (u * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hu)
  have hlarge : ∀ᶠ L : ℝ in atTop,
      |(∑ n ∈ Ioc ⌊Real.exp (u * L)⌋₊ ⌊Real.exp (v * L)⌋₊,
          vonMangoldt n / (n : ℝ) * (g (Real.log n / L) / L)) -
            (∫ t in u..v, g t)| ≤ B / L ^ 6 := by
    filter_upwards [hLower.eventually (eventually_ge_atTop y₀), eventually_gt_atTop (0 : ℝ)]
      with L hLy₀ hL
    have hcenter' : ∀ y ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
        |realPrimeReciprocalSum y - Real.log y - c| ≤ C / (u * L) ^ 5 := by
      intro y hy
      have hlog : u * L ≤ Real.log y := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (u * L)) hy.1
      have hpow := pow_le_pow_left₀ (mul_pos hu hL).le hlog 5
      exact (hy₀ y (hLy₀.trans hy.1)).trans
        (div_le_div_of_nonneg_left hC (pow_pos (mul_pos hu hL) _) hpow)
    have h := abs_logScale_primeReciprocal_error_le hL huv hg_diff hg_deriv
      K₀ K₁ c (C / (u * L) ^ 5) hK₀ hK₁ hcenter'
    apply h.trans_eq
    dsimp [B]
    field_simp
  refine ⟨B, hB, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hlarge, eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  simpa only [logScalePrimeReciprocalSum, Real.rpow_def_of_pos hx0,
    mul_comm (Real.log x) u, mul_comm (Real.log x) v] using hx

/-- The actual logarithmically scaled Mangoldt sum converges to the test
function integral. All distribution inputs are discharged. -/
theorem tendsto_logScalePrimeReciprocalSum
    (g : ℝ → ℝ) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v)) (K₀ K₁ : ℝ)
    (hK₀ : ∀ t ∈ Set.Icc u v, |g t| ≤ K₀)
    (hK₁ : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K₁) :
    Tendsto (logScalePrimeReciprocalSum g u v) atTop (𝓝 (∫ t in u..v, g t)) := by
  obtain ⟨B, _, hB⟩ := exists_logScalePrimeReciprocalSum_error_bound
    g u v hu huv hg_diff hg_deriv K₀ K₁ hK₀ hK₁
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hB
    (tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop))

theorem tendsto_logScalePrimeReciprocalSum_nat
    (g : ℝ → ℝ) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hg_diff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ g t)
    (hg_deriv : ContinuousOn (deriv g) (Set.Icc u v)) (K₀ K₁ : ℝ)
    (hK₀ : ∀ t ∈ Set.Icc u v, |g t| ≤ K₀)
    (hK₁ : ∀ t ∈ Set.Icc u v, |deriv g t| ≤ K₁) :
    Tendsto (fun X : ℕ => logScalePrimeReciprocalSum g u v X)
      atTop (𝓝 (∫ t in u..v, g t)) :=
  (tendsto_logScalePrimeReciprocalSum g u v hu huv hg_diff hg_deriv K₀ K₁ hK₀ hK₁).comp
    tendsto_natCast_atTop_atTop

/-- The actual Mangoldt sum for the rational middle-prime sieve integrand. -/
theorem tendsto_middlePrimeIntegrand_reciprocalSum
    (a u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hva : v < a) (ha : a ≤ 1) :
    Tendsto (logScalePrimeReciprocalSum (middlePrimeIntegrand a) u v) atTop
      (𝓝 ((1 / a) * Real.log (v / u) +
        ((1 - a) / a) * Real.log ((a - u) / (a - v)))) := by
  have hdiff : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ (middlePrimeIntegrand a) t := by
    intro t ht
    have ht0 : 0 < t := hu.trans_le ht.1
    have hta : t < a := ht.2.trans_lt hva
    exact (hasDerivAt_middlePrimeIntegrand a t (ht0.trans hta).ne' ht0.ne'
      (sub_pos.mpr hta).ne').differentiableAt
  have h := tendsto_logScalePrimeReciprocalSum (middlePrimeIntegrand a) u v hu huv hdiff
    (continuousOn_deriv_middlePrimeIntegrand a u v hu hva)
    (1 / (u * (a - v))) (1 / (a * u ^ 2) + (1 - a) / (a * (a - v) ^ 2))
    (fun t ht => abs_middlePrimeIntegrand_le a u v t hu hva ha ht)
    (fun t ht => abs_deriv_middlePrimeIntegrand_le a u v t hu hva ha ht)
  rwa [integral_middlePrimeIntegrand a u v hu huv hva] at h

theorem tendsto_middlePrimeIntegrand_reciprocalSum_nat
    (a u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hva : v < a) (ha : a ≤ 1) :
    Tendsto (fun X : ℕ => logScalePrimeReciprocalSum (middlePrimeIntegrand a) u v X) atTop
      (𝓝 ((1 / a) * Real.log (v / u) +
        ((1 - a) / a) * Real.log ((a - u) / (a - v)))) :=
  (tendsto_middlePrimeIntegrand_reciprocalSum a u v hu huv hva ha).comp
    tendsto_natCast_atTop_atTop

end TwinPrime.Analytic
