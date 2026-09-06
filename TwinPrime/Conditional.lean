import Mathlib
import TwinPrime.Basic
import TwinPrime.Brun

/-!
# Conditional results and corollaries

* `twinPrimeConjecture_of_tendsto` : `π₂(x) → ∞` implies the conjecture.
* `twinPrimeConjecture_of_lower_bound` : an eventual lower bound `c x/(log x)² ≤ π₂(x)` (`c > 0`)
  implies the conjecture.
* `HardyLittlewoodAsymptotic C` : the Hardy–Littlewood prediction `π₂(x) ∼ C x/(log x)²` (for the
  true constant `C = 2 ∏_{p>2}(1 - 1/(p-1)²) ≈ 1.3203`), and
  `twinPrimeConjecture_of_hardyLittlewood` : it implies the conjecture for any `C > 0`.
* `twinCount_div_tendsto_zero` : twin primes have density zero (corollary of Brun's bound).
* `brun_summable_pair` : `∑ (1/p + 1/(p+2))` over twin prime pairs converges, so **Brun's
  constant** `brunConstant` is a well-defined real number.

The point of the conditional theorems is to make the *gap* explicit: the conjecture follows from
any positive lower bound of the expected order, and every method known so far produces only
upper bounds of that order (`twinCount_le`).
-/

noncomputable section

open Filter Topology Finset Real

namespace TwinPrime

/-! ### Growth of `π₂` implies the conjecture -/

theorem twinPrimeConjecture_of_tendsto (h : Tendsto (fun x : ℕ => twinCount x) atTop atTop) :
    TwinPrimeConjecture := by
  by_contra hfin
  unfold TwinPrimeConjecture at hfin
  rw [Set.not_infinite] at hfin
  have hbound : ∀ x, twinCount x ≤ hfin.toFinset.card := by
    intro x
    unfold twinCount
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Set.Finite.mem_toFinset]
    exact hp.2
  obtain ⟨x, hx⟩ := (tendsto_atTop.mp h (hfin.toFinset.card + 1)).exists
  have := hbound x
  omega

/-- `x / (log x)^2 → ∞`. -/
theorem tendsto_div_log_sq_atTop :
    Tendsto (fun x : ℝ => x / (Real.log x) ^ 2) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using h0, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    have : 0 < Real.log x := Real.log_pos hx
    exact Set.mem_Ioi.mpr (by positivity)
  have h2 := h1.inv_tendsto_nhdsGT_zero
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [Pi.inv_apply, inv_div]

theorem twinPrimeConjecture_of_lower_bound {c : ℝ} (hc : 0 < c) (x₀ : ℕ)
    (h : ∀ x ≥ x₀, c * x / (Real.log x) ^ 2 ≤ twinCount x) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_tendsto
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  have hlow : Tendsto (fun x : ℕ => c * x / (Real.log x) ^ 2) atTop atTop := by
    have := (tendsto_div_log_sq_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
    refine this.congr' ?_
    filter_upwards with x
    simp only [Function.comp]
    ring
  refine tendsto_atTop_mono' atTop ?_ hlow
  rw [Filter.EventuallyLE, eventually_atTop]
  exact ⟨x₀, fun x hx => h x hx⟩

/-! ### The Hardy–Littlewood asymptotic implies the conjecture -/

/-- The Hardy–Littlewood twin prime asymptotic with constant `C`:
`π₂(x) / (C x / (log x)^2) → 1`.  (Conjecturally true with `C = 2 ∏_{p > 2} (1 - 1/(p-1)^2)`.) -/
def HardyLittlewoodAsymptotic (C : ℝ) : Prop :=
  Tendsto (fun x : ℕ => (twinCount x : ℝ) / (C * x / (Real.log x) ^ 2)) atTop (𝓝 1)

theorem twinPrimeConjecture_of_hardyLittlewood {C : ℝ} (hC : 0 < C)
    (h : HardyLittlewoodAsymptotic C) : TwinPrimeConjecture := by
  -- eventually the ratio is at least `1/2`
  have hev : ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (twinCount x : ℝ) / (C * x / (Real.log x) ^ 2) :=
    h.eventually (eventually_ge_nhds (by norm_num))
  rw [eventually_atTop] at hev
  obtain ⟨x₀, hx₀⟩ := hev
  apply twinPrimeConjecture_of_lower_bound (c := C / 2) (by positivity) (max x₀ 2)
  intro x hx
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hden : 0 < C * x / (Real.log x) ^ 2 := by positivity
  have := hx₀ x hx0
  rw [le_div_iff₀ hden] at this
  calc C / 2 * (x : ℝ) / (Real.log x) ^ 2 = 1 / 2 * (C * x / (Real.log x) ^ 2) := by ring
    _ ≤ (twinCount x : ℝ) := this

/-! ### Density zero -/

/-- Twin primes have density zero: `π₂(x) / x → 0`. -/
theorem twinCount_div_tendsto_zero :
    Tendsto (fun x : ℕ => (twinCount x : ℝ) / x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => (Real.log x) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hupper : Tendsto (fun x : ℕ => 2 ^ 33 / (Real.log x) ^ 2) atTop (𝓝 0) := by
    have := hlog.inv_tendsto_atTop.const_mul (2 ^ 33 : ℝ)
    simpa [div_eq_mul_inv] using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards with x
    positivity
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have h := twinCount_le hx
    rw [div_le_iff₀ hxpos]
    calc (twinCount x : ℝ) ≤ 2 ^ 33 * x / (Real.log x) ^ 2 := h
      _ = 2 ^ 33 / (Real.log x) ^ 2 * x := by ring

/-! ### Brun's constant -/

/-- The full reciprocal sum over twin prime *pairs* converges. -/
theorem brun_summable_pair :
    Summable (fun p : twinPrimes => (1 : ℝ) / p + 1 / ((p : ℕ) + 2)) := by
  have h := brun
  refine (h.add h).of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
  have hp : (0 : ℝ) < p := by exact_mod_cast (p.2.1.pos)
  have : (1 : ℝ) / ((p : ℕ) + 2) ≤ 1 / p := by
    apply one_div_le_one_div_of_le hp
    linarith
  linarith

/-- **Brun's constant** `B₂ = ∑_{(p, p+2) twin} (1/p + 1/(p+2)) ≈ 1.902160583…`. -/
def brunConstant : ℝ := ∑' p : twinPrimes, ((1 : ℝ) / p + 1 / ((p : ℕ) + 2))

theorem brunConstant_pos : 0 < brunConstant := by
  unfold brunConstant
  apply brun_summable_pair.tsum_pos (fun p => by positivity) ⟨3, three_mem⟩
  positivity

end TwinPrime
