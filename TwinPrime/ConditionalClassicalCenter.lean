import TwinPrime.Analytic.ClassicalCenterPrecision
import TwinPrime.Analytic.PrimePowerLogPrecision
import TwinPrime.Analytic.ClassicalDistribution

/-!
# A cofinal logarithmic gain above the finite classical center

The classical progression and prime-power errors are proved negligible at
every fixed logarithmic scale. Consequently a cofinal gain of `c X / log^k X`
above the exact finite center suffices. The displayed signed gain is an
unproved hypothesis; the theorem asserts neither that gain nor a positive
linear density of twin primes.
-/

noncomputable section

open Filter

namespace TwinPrime

open Analytic

/-- A cofinal, possibly sublinear, signed gain over the actual finite classical
center survives the proved progression and proper-prime-power errors. -/
theorem twinPrimeConjecture_of_cofinal_classicalCenter_log_gain
    (U V : ℕ → ℕ) (a : ℝ) (ha : 0 ≤ a) (haHalf : a < 1 / 2)
    (hU : ∀ᶠ X : ℕ in atTop, 1 ≤ U X)
    (hV : ∀ᶠ X : ℕ in atTop, 1 ≤ V X)
    (hUV : ∀ᶠ X : ℕ in atTop, ((U X * V X : ℕ) : ℝ) ≤ (X : ℝ) ^ a)
    (c : ℝ) (hc : 0 < c) (k : ℕ)
    (hgain : ∀ Y : ℕ, ∃ X ≥ Y,
      c * (X : ℝ) / Real.log (2 * X + 2) ^ k ≤
        bilinearTerm (U X) (V X) X + classicalCorrelationCenter (U X) (V X) X) :
    TwinPrimeConjecture := by
  let F : ℕ → ℝ := fun X =>
    bilinearTerm (U X) (V X) X + classicalCorrelationCenter (U X) (V X) X
  have herr := maximal_bombieri_vinogradov.tendsto_classicalCenter_error_div_mul_log_pow
    U V a ha haHalf hU hV hUV k
  have htotal : Tendsto (fun X : ℕ =>
      (|W2 X - F X| + Epp X) / X * Real.log (2 * X + 2) ^ k)
      atTop (nhds 0) := by
    simpa only [F, add_div, add_mul, zero_add] using
      herr.add (tendsto_Epp_div_mul_log_pow k)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (htotal.eventually (gt_mem_nhds hc))
  apply twinPrimeConjecture_of_cofinal_W2_gt_Epp
  intro Y
  obtain ⟨X, hX, hFX⟩ := hgain (max Y (max X₀ 1))
  have hYX : Y ≤ X := (le_max_left _ _).trans hX
  have hX₀X : X₀ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hX1 : 1 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hx : (0 : ℝ) < X := by exact_mod_cast hX1
  have hlog : 0 < Real.log (2 * (X : ℝ) + 2) := by
    apply Real.log_pos
    linarith
  have hp : 0 < Real.log (2 * (X : ℝ) + 2) ^ k := pow_pos hlog k
  have hscaled : (|W2 X - F X| + Epp X) * Real.log (2 * X + 2) ^ k < c * X := by
    calc
      _ = ((|W2 X - F X| + Epp X) / X * Real.log (2 * X + 2) ^ k) * X := by
        field_simp
      _ < c * X := mul_lt_mul_of_pos_right (hX₀ X hX₀X) hx
  have hsmall : |W2 X - F X| + Epp X < c * X / Real.log (2 * X + 2) ^ k :=
    (lt_div_iff₀ hp).mpr hscaled
  have hF : |W2 X - F X| + Epp X < F X := hsmall.trans_le hFX
  have hlow := neg_abs_le (W2 X - F X)
  exact ⟨X, hYX, by linarith⟩

end TwinPrime
