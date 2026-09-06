import TwinPrime.Analytic.QuadraticProductCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite positive sums for the quadratic product

These are actual finite Dirichlet sums of the proved convolution coefficients.
The lower bound one holds on either side of the line of absolute convergence;
no identification with an infinite series below that line is made.
-/

noncomputable section

open Finset
open scoped ComplexOrder

namespace TwinPrime.Analytic

def quadraticProductRealPartialSum {q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ q)
    (σ : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 X, (n : ℝ) ^ (-σ) * (quadraticProductCoefficients χ₁ χ₂ n).re

def quadraticProductDirichletPartialSum {q : ℕ} (χ₁ χ₂ : DirichletCharacter ℂ q)
    (s : ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 X, (n : ℂ) ^ (-s) * quadraticProductCoefficients χ₁ χ₂ n

theorem quadraticProductCoefficients_eq_ofReal_re {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (n : ℕ) :
    quadraticProductCoefficients χ₁ χ₂ n = ((quadraticProductCoefficients χ₁ χ₂ n).re : ℂ) := by
  have him := (Complex.nonneg_iff.mp (quadraticProductCoefficients_nonneg hχ₁ hχ₂ n)).2
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using him.symm

theorem quadraticProductDirichletPartialSum_real {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (σ : ℝ) (X : ℕ) :
    quadraticProductDirichletPartialSum χ₁ χ₂ (σ : ℂ) X =
      (quadraticProductRealPartialSum χ₁ χ₂ σ X : ℂ) := by
  unfold quadraticProductDirichletPartialSum quadraticProductRealPartialSum
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n _
  rw [quadraticProductCoefficients_eq_ofReal_re hχ₁ hχ₂ n,
    ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

theorem quadraticProductRealPartialSum_nonneg {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (σ : ℝ) (X : ℕ) : 0 ≤ quadraticProductRealPartialSum χ₁ χ₂ σ X := by
  apply sum_nonneg
  intro n _
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Complex.nonneg_iff.mp (quadraticProductCoefficients_nonneg hχ₁ hχ₂ n)).1

/-- The coefficient at one gives a uniform lower bound for every real
exponent and every positive finite cutoff. -/
theorem one_le_quadraticProductRealPartialSum {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (σ : ℝ) (X : ℕ) (hX : 1 ≤ X) : 1 ≤ quadraticProductRealPartialSum χ₁ χ₂ σ X := by
  have hterm : (1 : ℝ) ^ (-σ) * (quadraticProductCoefficients χ₁ χ₂ 1).re ≤
      quadraticProductRealPartialSum χ₁ χ₂ σ X := by
    have h := single_le_sum
      (f := fun n : ℕ => (n : ℝ) ^ (-σ) * (quadraticProductCoefficients χ₁ χ₂ n).re)
      (s := Ioc 0 X)
      (fun n _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Complex.nonneg_iff.mp (quadraticProductCoefficients_nonneg hχ₁ hχ₂ n)).1)
      (a := 1) (mem_Ioc.mpr ⟨by norm_num, hX⟩)
    simpa only [Nat.cast_one, quadraticProductRealPartialSum] using h
  simpa only [Real.one_rpow, quadraticProductCoefficients_one, Complex.one_re, mul_one] using hterm

theorem quadraticProductRealPartialSum_mono {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (σ : ℝ) : Monotone (quadraticProductRealPartialSum χ₁ χ₂ σ) := by
  intro X Y hXY
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hXY⟩
  · intro n _ _
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Complex.nonneg_iff.mp (quadraticProductCoefficients_nonneg hχ₁ hχ₂ n)).1

theorem one_le_quadraticProductDirichletPartialSum {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1)
    (σ : ℝ) (X : ℕ) (hX : 1 ≤ X) :
    (1 : ℂ) ≤ quadraticProductDirichletPartialSum χ₁ χ₂ (σ : ℂ) X := by
  rw [quadraticProductDirichletPartialSum_real hχ₁ hχ₂]
  exact_mod_cast one_le_quadraticProductRealPartialSum hχ₁ hχ₂ σ X hX

end TwinPrime.Analytic
