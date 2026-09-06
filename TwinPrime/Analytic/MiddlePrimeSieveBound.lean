import TwinPrime.Analytic.MiddlePrimeMainLimit
import TwinPrime.Analytic.MiddlePrimeSieveConstant

/-!
# An unconditional bound for the complete negative middle-prime class

The actual prime main sum, weighted error and integer thresholds are all
supplied. A fixed level exponent below one half gives the required strict
margin for the right cutoff exponent `21/100`. This bounds one negative
class; it is not a signed bilinear lower bound or a twin-prime theorem.
-/

noncomputable section

open Filter Topology

namespace TwinPrime.Analytic

/-- Every positive margin above the explicit main constant eventually
bounds the normalized mass of the complete middle-prime class. -/
theorem eventually_middlePrimePowerMass_div_le
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      middlePrimeMass (primaryCutoff X) (middlePrimePowerCutoff v X) X / (X : ℝ) ≤
        (2 * twinPrimeConstant) * middlePrimeSieveMainConstant a v + ε := by
  let A := middlePrimeSieveMainConstant a v
  let C := 2 * twinPrimeConstant
  let δ := ε / (2 * (|A| + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmass : δ * (|A| + 1) = ε / 2 := by
    dsimp [δ]
    have hn : |A| + 1 ≠ 0 := by positivity
    field_simp
  have hδA : δ * A ≤ δ * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hδ.le
  have hmargin : (C + δ) * A < C * A + ε := by nlinarith
  have hmain : Tendsto (middlePrimePowerMainSum a v) atTop (𝓝 A) := by
    simpa only [A, middlePrimeSieveMainConstant] using
      tendsto_middlePrimePowerMainSum a v hv hva ha
  have herr := tendsto_middlePrimePowerSieveFullError_div a v hv hva ha
  have hlim := (hmain.const_mul (C + δ)).add herr
  simp only [add_zero] at hlim
  filter_upwards [eventually_middlePrimePowerMass_div_le_main_add_error a v hv hva ha δ hδ,
    hlim.eventually (gt_mem_nhds hmargin)] with X hbound hsmall
  exact hbound.trans hsmall.le

/-- Unnormalized form, with the positive endpoint handled explicitly. -/
theorem eventually_middlePrimePowerMass_le
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      middlePrimeMass (primaryCutoff X) (middlePrimePowerCutoff v X) X ≤
        ((2 * twinPrimeConstant) * middlePrimeSieveMainConstant a v + ε) * X := by
  filter_upwards [eventually_middlePrimePowerMass_div_le a v hv hva ha ε hε,
    eventually_ge_atTop 1] with X hbound hX
  exact (div_le_iff₀ (show (0 : ℝ) < X by exact_mod_cast hX)).mp hbound

/-- The complete negative class with right exponent `21/100` has mass at
most `0.263 C X` eventually, using only proved arithmetic inputs. -/
theorem eventually_middlePrimeMass_twentyOneHundredths_le :
    ∀ᶠ X : ℕ in atTop,
      middlePrimeMass (primaryCutoff X) (middlePrimePowerCutoff (21 / 100) X) X ≤
        (263 / 1000 : ℝ) * (2 * twinPrimeConstant) * X := by
  let a : ℝ := 49999 / 100000
  let v : ℝ := 21 / 100
  let C := 2 * twinPrimeConstant
  have hC : 0 < C := mul_pos (by norm_num) twinPrimeConstant_pos
  have hA : middlePrimeSieveMainConstant a v < 263 / 1000 :=
    middlePrimeSieveMainConstant_fixed_lt
  let ε := C * (263 / 1000 - middlePrimeSieveMainConstant a v)
  have hε : 0 < ε := mul_pos hC (sub_pos.mpr hA)
  have h := eventually_middlePrimePowerMass_le a v (by norm_num [v])
    (by norm_num [a, v]) (by norm_num [a]) ε hε
  filter_upwards [h] with X hX
  convert! hX using 1
  dsimp [ε, C]
  ring

end TwinPrime.Analytic
