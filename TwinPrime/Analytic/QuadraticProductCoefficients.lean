import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Positive coefficients of a four-factor quadratic L-series

The product is Dirichlet convolution, not pointwise multiplication. At a
prime where one character is negative, pairing its zeta convolution with
the twisted copy makes the even-exponent support explicit. At every other
prime the relevant twist is nonnegative. These finite identities prove
nonnegative real coefficients and the square-coefficient lower bound.
-/

noncomputable section

open ArithmeticFunction Finset
open scoped ComplexOrder

namespace TwinPrime.Analytic

def quadraticProductCoefficients {Q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    ArithmeticFunction ℂ :=
  .zeta * toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
    toArithmeticFunction ((χ₁ * χ₂) ·)

theorem quadraticProductCoefficients_isMultiplicative {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    (quadraticProductCoefficients χ₁ χ₂).IsMultiplicative :=
  ((χ₁.isMultiplicative_zetaMul.mul χ₂.isMultiplicative_toArithmeticFunction).mul
    (χ₁ * χ₂).isMultiplicative_toArithmeticFunction)

@[simp] theorem quadraticProductCoefficients_one {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) : quadraticProductCoefficients χ₁ χ₂ 1 = 1 :=
  (quadraticProductCoefficients_isMultiplicative χ₁ χ₂).map_one

theorem quadraticProductCoefficients_comm {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    quadraticProductCoefficients χ₁ χ₂ = quadraticProductCoefficients χ₂ χ₁ := by
  unfold quadraticProductCoefficients
  rw [show χ₂ * χ₁ = χ₁ * χ₂ from mul_comm _ _]
  ac_rfl

theorem quadraticProductCoefficients_eq_paired {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) :
    quadraticProductCoefficients χ₁ χ₂ = χ₁.zetaMul *
      (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) := by
  unfold quadraticProductCoefficients DirichletCharacter.zetaMul
  exact mul_assoc _ _ _

/-- An exact finite convolution identity: the other two character factors
are a pointwise twist of the first character's zeta convolution. -/
theorem character_pair_convolution_eq_twisted_zetaMul {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (n : ℕ) :
    (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) n =
      χ₂ n * χ₁.zetaMul n := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hd
  have hm := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd
  have hk := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd
  rw [← hprod]
  simp only [toArithmeticFunction, coe_mk, hm, hk, if_false, natCoe_apply,
    zeta_apply_ne hm, Nat.cast_one, one_mul, Nat.cast_mul, map_mul, MulChar.mul_apply]
  ring

theorem zetaMul_prime_pow_eq_sum {Q : ℕ} (χ : DirichletCharacter ℂ Q)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    χ.zetaMul (p ^ k) = ∑ i ∈ range (k + 1), χ p ^ i := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and,
    if_false, Nat.cast_pow, map_pow]

/-- Nonnegative local factors give a nonnegative Dirichlet convolution at
every power of the same prime. -/
theorem arithmeticFunction_mul_prime_pow_nonneg (f g : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (hf : ∀ k, 0 ≤ f (p ^ k)) (hg : ∀ k, 0 ≤ g (p ^ k))
    (k : ℕ) : 0 ≤ (f * g) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_nonneg
  intro d hd
  obtain ⟨i, _, hi⟩ := (Nat.mem_divisors_prime_pow hp k).mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hd)
  obtain ⟨j, _, hj⟩ := (Nat.mem_divisors_prime_pow hp k).mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hd)
  rw [hi, hj]
  exact mul_nonneg (hf i) (hg j)

/-- The last convolution includes the endpoint divisor with complementary
factor one; all other local terms are nonnegative. -/
theorem arithmeticFunction_le_mul_prime_pow (f g : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (hf : ∀ k, 0 ≤ f (p ^ k)) (hg : ∀ k, 0 ≤ g (p ^ k))
    (hg1 : g 1 = 1) (k : ℕ) : f (p ^ k) ≤ (f * g) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply]
  have hterm : f (p ^ k) * g 1 ≤
      ∑ d ∈ (p ^ k).divisorsAntidiagonal, f d.1 * g d.2 := by
    apply single_le_sum (f := fun d : ℕ × ℕ => f d.1 * g d.2)
      (s := (p ^ k).divisorsAntidiagonal) (a := (p ^ k, 1))
    · intro d hd
      obtain ⟨i, _, hi⟩ := (Nat.mem_divisors_prime_pow hp k).mp
        (Nat.fst_mem_divisors_of_mem_antidiagonal hd)
      obtain ⟨j, _, hj⟩ := (Nat.mem_divisors_prime_pow hp k).mp
        (Nat.snd_mem_divisors_of_mem_antidiagonal hd)
      rw [hi, hj]
      exact mul_nonneg (hf i) (hg j)
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one _, pow_ne_zero _ hp.ne_zero⟩
  simpa only [hg1, mul_one] using hterm

theorem character_pair_prime_pow_nonneg_of_nonneg {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (hχ₁ : χ₁ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (hχ₂p : 0 ≤ χ₂ p) (k : ℕ) :
    0 ≤ (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) (p ^ k) := by
  rw [character_pair_convolution_eq_twisted_zetaMul, Nat.cast_pow, map_pow]
  exact mul_nonneg (pow_nonneg hχ₂p _) (DirichletCharacter.zetaMul_prime_pow_nonneg hχ₁ hp k)

/-- The alternating zeta convolution vanishes at odd exponents. At even
exponents its quadratic twist is nonnegative. -/
theorem character_pair_prime_pow_nonneg_of_neg_one {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (hχ₂ : χ₂ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (hχ₁p : χ₁ p = -1) (k : ℕ) :
    0 ≤ (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) (p ^ k) := by
  rw [character_pair_convolution_eq_twisted_zetaMul, Nat.cast_pow, map_pow,
    zetaMul_prime_pow_eq_sum χ₁ hp k, hχ₁p, neg_one_geom_sum]
  split_ifs with hk
  · simp only [mul_zero, le_refl]
  · rw [mul_one]
    have heven : Even k := by simpa only [Nat.even_add_one, Nat.not_odd_iff_even, not_not] using hk
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ₂ p with h | h | h
    · rw [h]
      exact pow_nonneg le_rfl _
    · simp only [h, one_pow, zero_le_one]
    · simp only [h, heven.neg_one_pow, zero_le_one]

theorem one_le_zetaMul_prime_even_pow {Q : ℕ}
    (χ : DirichletCharacter ℂ Q) (hχ : χ ^ 2 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    1 ≤ χ.zetaMul (p ^ (2 * k)) := by
  rw [zetaMul_prime_pow_eq_sum χ hp]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · have hterm : χ p ^ 0 ≤ ∑ i ∈ range (2 * k + 1), χ p ^ i :=
      single_le_sum (fun i _ => pow_nonneg (by rw [h]) _) (mem_range.mpr (by omega))
    simpa only [pow_zero] using hterm
  · have hterm : χ p ^ 0 ≤ ∑ i ∈ range (2 * k + 1), χ p ^ i :=
      single_le_sum (fun i _ => pow_nonneg (by rw [h]; exact zero_le_one) _)
        (mem_range.mpr (by omega))
    simpa only [pow_zero] using hterm
  · rw [h, neg_one_geom_sum, if_neg (by simp)]

private theorem quadraticProductCoefficients_local_of_pair {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (hχ₁ : χ₁ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime)
    (hpair : ∀ k, 0 ≤
      (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) (p ^ k)) :
    (∀ k, 0 ≤ quadraticProductCoefficients χ₁ χ₂ (p ^ k)) ∧
      ∀ k, 1 ≤ quadraticProductCoefficients χ₁ χ₂ (p ^ (2 * k)) := by
  have hf := fun k => DirichletCharacter.zetaMul_prime_pow_nonneg hχ₁ hp k
  have hg1 : (toArithmeticFunction (χ₂ ·) * toArithmeticFunction ((χ₁ * χ₂) ·)) 1 = 1 := by
    simp [toArithmeticFunction]
  constructor
  · intro k
    rw [quadraticProductCoefficients_eq_paired]
    exact arithmeticFunction_mul_prime_pow_nonneg _ _ hp hf hpair k
  · intro k
    rw [quadraticProductCoefficients_eq_paired]
    exact (one_le_zetaMul_prime_even_pow χ₁ hχ₁ hp k).trans
      (arithmeticFunction_le_mul_prime_pow _ _ hp hf hpair hg1 (2 * k))

theorem quadraticProductCoefficients_prime_pow_bounds {Q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ Q) (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) :
    (∀ k, 0 ≤ quadraticProductCoefficients χ₁ χ₂ (p ^ k)) ∧
      ∀ k, 1 ≤ quadraticProductCoefficients χ₁ χ₂ (p ^ (2 * k)) := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ₂ p with h | h | h
  · exact quadraticProductCoefficients_local_of_pair χ₁ χ₂ hχ₁ hp
      (character_pair_prime_pow_nonneg_of_nonneg χ₁ χ₂ hχ₁ hp (by rw [h]))
  · exact quadraticProductCoefficients_local_of_pair χ₁ χ₂ hχ₁ hp
      (character_pair_prime_pow_nonneg_of_nonneg χ₁ χ₂ hχ₁ hp (by rw [h]; exact zero_le_one))
  · rw [quadraticProductCoefficients_comm χ₁ χ₂]
    exact quadraticProductCoefficients_local_of_pair χ₂ χ₁ hχ₂ hp
      (character_pair_prime_pow_nonneg_of_neg_one χ₂ χ₁ hχ₁ hp h)

/-- Every coefficient is a nonnegative real number, in `ComplexOrder`. -/
theorem quadraticProductCoefficients_nonneg {Q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ Q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ quadraticProductCoefficients χ₁ χ₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · rw [(quadraticProductCoefficients_isMultiplicative χ₁ χ₂).multiplicative_factorization _ hn]
    exact prod_nonneg fun p hp => (quadraticProductCoefficients_prime_pow_bounds χ₁ χ₂ hχ₁ hχ₂
      (Nat.prime_of_mem_primeFactors hp)).1 _

/-- Every nonzero square coefficient is at least one. -/
theorem one_le_quadraticProductCoefficients_square {Q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ Q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (n : ℕ) (hn : n ≠ 0) : 1 ≤ quadraticProductCoefficients χ₁ χ₂ (n ^ 2) := by
  rw [(quadraticProductCoefficients_isMultiplicative χ₁ χ₂).multiplicative_factorization _
    (pow_ne_zero _ hn)]
  apply Finset.one_le_prod
  intro p hp
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  exact (quadraticProductCoefficients_prime_pow_bounds χ₁ χ₂ hχ₁ hχ₂
    (Nat.prime_of_mem_primeFactors hp)).2 _

end TwinPrime.Analytic
