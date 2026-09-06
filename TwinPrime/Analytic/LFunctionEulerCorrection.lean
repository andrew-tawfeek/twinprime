import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!

# Logarithmic derivatives of induced Dirichlet L-functions

The exact change-of-modulus identity is differentiated with all Euler
denominators justified.  The resulting finite correction has norm at most
the logarithm of the larger positive modulus on `1 < s.re`.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/-- The finite correction uses the prime factors of the larger modulus. -/
def characterEulerCorrection {M : ℕ} (χ : DirichletCharacter ℂ M)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ N.primeFactors,
    χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - χ p * (p : ℂ) ^ (-s))

@[simp] theorem characterEulerCorrection_one {M : ℕ}
    (χ : DirichletCharacter ℂ M) (s : ℂ) : characterEulerCorrection χ 1 s = 0 := by
  simp [characterEulerCorrection]

/-- A uniform smallness bound for every prime Euler ratio. -/
theorem norm_characterEulerRatio_le_half {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
  calc
    _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-s.re) := one_mul _
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hs)
    _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2

/-- Euler denominators are nonzero already on the boundary `s.re=1`. -/
theorem characterEulerFactor_ne_zero {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  have h := norm_characterEulerRatio_le_half χ p hp s hs
  intro heq
  have hz : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -heq
  rw [hz, norm_one] at h
  norm_num at h

/-- Differentiation of one Euler factor with the real prime logarithm. -/
theorem hasDerivAt_characterEulerFactor {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 0 < p) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z))
      (χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s)) s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := (((hasDerivAt_id s).neg.const_cpow (c := (p : ℂ))
    (Or.inl hp0)).const_mul (χ p)).const_sub (1 : ℂ)
  simpa only [id_eq, Pi.neg_apply, ← Complex.natCast_log, neg_mul, mul_neg,
    mul_one, one_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using h

/-- Each Euler logarithmic-derivative term is bounded by the prime logarithm. -/
theorem norm_characterEulerTerm_le_log {M : ℕ} (χ : DirichletCharacter ℂ M)
    (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) /
        (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ Real.log p := by
  let z : ℂ := χ p * (p : ℂ) ^ (-s)
  have hz : ‖z‖ ≤ 1 / 2 := norm_characterEulerRatio_le_half χ p hp s hs
  have hd : 1 / 2 ≤ ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    linarith
  have hdpos : 0 < ‖1 - z‖ := by linarith
  have hn : ‖z‖ ≤ ‖1 - z‖ := hz.trans hd
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have heq : χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-s) = z * (Real.log p : ℂ) := by
    dsimp [z]
    ring
  rw [heq]
  change ‖z * (Real.log p : ℂ) / (1 - z)‖ ≤ Real.log p
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  apply (div_le_iff₀ hdpos).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn hlog]

/-- The logarithms of the distinct prime factors are bounded by that of
their positive parent modulus.  Modulus one has an empty sum. -/
theorem sum_log_primeFactors_le_log (N : ℕ) (hN : 0 < N) :
    (∑ p ∈ N.primeFactors, Real.log p) ≤ Real.log N := by
  have hp (p : ℕ) (hp : p ∈ N.primeFactors) : (0 : ℝ) < p := by
    exact_mod_cast Nat.pos_of_mem_primeFactors hp
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)

/-- A finite, conductor-uniform bound for the entire inducing correction. -/
theorem norm_characterEulerCorrection_le_log {M : ℕ} (χ : DirichletCharacter ℂ M)
    (N : ℕ) (hN : 0 < N) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖characterEulerCorrection χ N s‖ ≤ Real.log N := by
  unfold characterEulerCorrection
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum fun p hp => norm_characterEulerTerm_le_log χ p
    (Nat.prime_of_mem_primeFactors hp).two_le s hs).trans
  exact sum_log_primeFactors_le_log N hN

/-- Differentiate the actual inducing Euler product; all characters,
including the principal character at conductor one, are allowed. -/
theorem logDerivative_LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction (χ.changeLevel hMN)) s /
        DirichletCharacter.LFunction (χ.changeLevel hMN) s =
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s +
        characterEulerCorrection χ N s := by
  have hs1 : s ≠ 1 := by intro heq; simp [heq] at hs
  let F : ℂ → ℂ := fun z => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))
  have hf (p : ℕ) (hp : p ∈ N.primeFactors) :
      1 - χ p * (p : ℂ) ^ (-s) ≠ 0 :=
    characterEulerFactor_ne_zero χ p (Nat.prime_of_mem_primeFactors hp).two_le s hs.le
  have hd (p : ℕ) (hp : p ∈ N.primeFactors) :
      DifferentiableAt ℂ (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s :=
    (hasDerivAt_characterEulerFactor χ p (Nat.pos_of_mem_primeFactors hp) s).differentiableAt
  have hF : F s ≠ 0 := prod_ne_zero_iff.mpr hf
  have hdF : DifferentiableAt ℂ F s := DifferentiableAt.fun_finsetProd hd
  have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hdL := DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs1)
  have heq : DirichletCharacter.LFunction (χ.changeLevel hMN) =ᶠ[𝓝 s]
      (fun z => DirichletCharacter.LFunction χ z * F z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hz)
  have hprod : logDeriv F s = characterEulerCorrection χ N s := by
    rw [show F = (fun z => ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))) from rfl,
      logDeriv_prod hf hd]
    unfold characterEulerCorrection
    apply sum_congr rfl
    intro p hp
    rw [logDeriv_apply, (hasDerivAt_characterEulerFactor χ p
      (Nat.pos_of_mem_primeFactors hp) s).deriv]
  rw [heq.deriv_eq, heq.eq_of_nhds]
  change logDeriv (fun z => DirichletCharacter.LFunction χ z * F z) s = _
  rw [logDeriv_mul s hL hF hdL hdF, hprod, logDeriv_apply]

/-- The induced and inducing logarithmic derivatives differ by at most
the logarithm of the larger modulus. -/
theorem norm_logDerivative_LFunction_changeLevel_sub_le {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    ‖deriv (DirichletCharacter.LFunction (χ.changeLevel hMN)) s /
        DirichletCharacter.LFunction (χ.changeLevel hMN) s -
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        Real.log N := by
  rw [logDerivative_LFunction_changeLevel hMN χ s hs, add_sub_cancel_left]
  exact norm_characterEulerCorrection_le_log χ N (NeZero.pos N) s hs.le

/-- The negative logarithmic derivative has the opposite correction sign. -/
theorem neg_logDerivative_LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction (χ.changeLevel hMN)) s /
        DirichletCharacter.LFunction (χ.changeLevel hMN) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        characterEulerCorrection χ N s := by
  rw [neg_div, neg_div, logDerivative_LFunction_changeLevel hMN χ s hs]
  ring

/-- Every positive-modulus character can be compared to its actual primitive
inducing character, including a principal inducing character of conductor one. -/
theorem logDerivative_LFunction_eq_primitiveCharacter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : 1 < s.re) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      deriv (DirichletCharacter.LFunction χ.primitiveCharacter) s /
        DirichletCharacter.LFunction χ.primitiveCharacter s +
      characterEulerCorrection χ.primitiveCharacter N s := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [χ.changeLevel_primitiveCharacter] using
    logDerivative_LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter s hs

/-- Quantitative induction to the primitive character, with no primitivity
assumption on the original character or its powers. -/
theorem norm_logDerivative_LFunction_sub_primitiveCharacter_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : 1 < s.re) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
      deriv (DirichletCharacter.LFunction χ.primitiveCharacter) s /
        DirichletCharacter.LFunction χ.primitiveCharacter s‖ ≤ Real.log N := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [logDerivative_LFunction_eq_primitiveCharacter χ s hs, add_sub_cancel_left]
  exact norm_characterEulerCorrection_le_log χ.primitiveCharacter N (NeZero.pos N) s hs.le

end TwinPrime.Analytic
