import TwinPrime.Analytic.QuadraticCenteredContinuation
import TwinPrime.Analytic.ZetaRealTruncation
import TwinPrime.Analytic.ResidueCutoff
import TwinPrime.Analytic.ResidueConductorBound

/-!
# Quantitative comparison with the actual quadratic-product residue

Subtracting the residue from the coefficients gives a convergent ordered
series below one. Its tail, the actual zeta truncation, and finite coefficient
positivity imply a residue lower bound at an actual real zero of the product.
The common-modulus and three nonprincipal conditions remain explicit.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- A weighted comparison retaining the actual product value and zeta term. -/
theorem norm_quadraticProductPartialSum_sub_product_sub_residue_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1) :
    ‖quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M -
      quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
        ((∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ))‖ ≤
      18522 * (1 + 3250 * (q : ℝ) ^ 2) * (M : ℝ) ^ (-(1 / 20 : ℝ)) := by
  have h := norm_centeredQuadraticLFunctionProduct_real_sub_partialSum_le
    χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ M hM β hβ hβ1.le
  rw [centeredQuadraticLFunctionProduct_eq_of_ne_one χ₁ χ₂ (β : ℂ)
    (by exact_mod_cast (ne_of_lt hβ1)),
    powerDirichletPartialSum_centeredQuadraticProductCoefficients] at h
  have heq : quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
      regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * riemannZeta (β : ℂ) -
      (quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
          (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ)))) =
      -(quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M -
        quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
          ((∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ))) := by ring
  rwa [heq, norm_neg] at h

theorem one_le_norm_quadraticProductDirichletPartialSum {q : ℕ}
    {χ₁ χ₂ : DirichletCharacter ℂ q} (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (β : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    1 ≤ ‖quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M‖ := by
  rw [quadraticProductDirichletPartialSum_real hsq₁ hsq₂,
    Complex.norm_real, Real.norm_eq_abs]
  exact (one_le_quadraticProductRealPartialSum hsq₁ hsq₂ β M hM).trans (le_abs_self _)

/-- A numerical tail budget yields a lower bound for the actual residue at
an actual zero; it does not assume a residue lower bound. -/
theorem quadraticProduct_residue_lower_bound_of_nonpos
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hF : (quadraticLFunctionProduct χ₁ χ₂ (β : ℂ)).re ≤ 0)
    (herror : 18522 * (1 + 3250 * (q : ℝ) ^ 2) *
      (M : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 / 2) :
    (1 - β) / (4 * (M : ℝ) ^ (1 - β)) ≤
      ‖regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ := by
  let T := quadraticProductDirichletPartialSum χ₁ χ₂ (β : ℂ) M
  let F := quadraticLFunctionProduct χ₁ χ₂ (β : ℂ)
  let L := regularizedQuadraticLFunctionProduct χ₁ χ₂ 1
  let B := (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-(β : ℂ))) - riemannZeta (β : ℂ)
  let R := T - F - L * B
  have hβ0 : 0 < β := by linarith
  have hδ : 0 < 1 - β := sub_pos.mpr hβ1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have htail : ‖R‖ ≤ (1 / 2 : ℝ) :=
    (norm_quadraticProductPartialSum_sub_product_sub_residue_le
      χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ M hM β hβ hβ1).trans herror
  have hB : ‖B‖ ≤ 2 * (M : ℝ) ^ (1 - β) / (1 - β) :=
    norm_zeta_real_sum_sub_zeta_le M hM β hβ0 hβ1
  have hT : (1 : ℝ) ≤ T.re := by
    simpa only [T, quadraticProductDirichletPartialSum_real hsq₁ hsq₂, Complex.ofReal_re] using
      one_le_quadraticProductRealPartialSum hsq₁ hsq₂ β M hM
  have hdecomp : T = F + L * B + R := by dsimp [R]; ring
  have hre : T.re = F.re + (L * B).re + R.re := by rw [hdecomp, Complex.add_re, Complex.add_re]
  have hR : R.re ≤ (1 / 2 : ℝ) := (Complex.re_le_norm R).trans htail
  have hprod : (L * B).re ≤ ‖L‖ * (2 * (M : ℝ) ^ (1 - β) / (1 - β)) := by
    apply (Complex.re_le_norm (L * B)).trans
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hB (norm_nonneg L)
  have hhalf : (1 / 2 : ℝ) ≤ ‖L‖ * (2 * (M : ℝ) ^ (1 - β) / (1 - β)) := by
    change F.re ≤ 0 at hF
    linarith
  have hscaled : (1 / 2 : ℝ) * (1 - β) ≤ ‖L‖ * (2 * (M : ℝ) ^ (1 - β)) := by
    apply (le_div_iff₀ hδ).mp
    simpa only [mul_div_assoc] using hhalf
  apply (div_le_iff₀ (mul_pos (by norm_num) (Real.rpow_pos_of_pos hM0 _))).mpr
  change 1 - β ≤ ‖L‖ * (4 * (M : ℝ) ^ (1 - β))
  nlinarith

theorem quadraticProduct_residue_lower_bound_of_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hzero : quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) = 0)
    (herror : 18522 * (1 + 3250 * (q : ℝ) ^ 2) *
      (M : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 / 2) :
    (1 - β) / (4 * (M : ℝ) ^ (1 - β)) ≤
      ‖regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ :=
  quadraticProduct_residue_lower_bound_of_nonpos χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hsq₁ hsq₂
    M hM β hβ hβ1 (by simp [hzero]) herror

theorem quadraticProduct_residue_lower_bound_at_cutoff_of_nonpos
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hF : (quadraticLFunctionProduct χ₁ χ₂ (β : ℂ)).re ≤ 0) :
    (1 - β) / (4 * (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) ^ (1 - β)) ≤
      ‖regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ := by
  have hC : (1 : ℝ) ≤ 1 + 3250 * (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  exact quadraticProduct_residue_lower_bound_of_nonpos χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hsq₁ hsq₂
    (residueCutoff (1 + 3250 * (q : ℝ) ^ 2)) (one_le_residueCutoff _ hC)
    β hβ hβ1 hF (residueCutoff_error_le_half _ hC)

/-- The explicit natural cutoff discharges the entire numerical tail budget. -/
theorem quadraticProduct_residue_lower_bound_at_cutoff_of_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hzero : quadraticLFunctionProduct χ₁ χ₂ (β : ℂ) = 0) :
    (1 - β) / (4 * (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) ^ (1 - β)) ≤
      ‖regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ := by
  have hC : (1 : ℝ) ≤ 1 + 3250 * (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  exact quadraticProduct_residue_lower_bound_of_zero χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hsq₁ hsq₂
    (residueCutoff (1 + 3250 * (q : ℝ) ^ 2)) (one_le_residueCutoff _ hC)
    β hβ hβ1 hzero (residueCutoff_error_le_half _ hC)

/-- An actual zero of the first nonprincipal quadratic character supplies the
product zero; distinctness supplies the third nonprincipal condition. -/
theorem quadraticProduct_residue_lower_bound_of_LFunction_zero
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1) (hne : χ₁ ≠ χ₂)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ₁ (β : ℂ) = 0) :
    (1 - β) / (4 * (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) ^ (1 - β)) ≤
      ‖regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ := by
  apply quadraticProduct_residue_lower_bound_at_cutoff_of_zero χ₁ χ₂ hχ₁ hχ₂
    (quadratic_character_mul_ne_one_of_ne χ₁ χ₂ hsq₁ hne) hsq₁ hsq₂ β hβ hβ1
  simp [quadraticLFunctionProduct, hzero]

/-- The ceiling cutoff has an explicit fortieth-power conductor bound. -/
theorem quadraticProduct_residue_conductor_lower_bound_of_nonpos
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hF : (quadraticLFunctionProduct χ₁ χ₂ (β : ℂ)).re ≤ 0) :
    (1 - β) / (4 * residueConductorConstant ^ (1 - β) * (q : ℝ) ^ (40 * (1 - β))) ≤
      ‖regularizedQuadraticLFunctionProduct χ₁ χ₂ 1‖ := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact (residue_gap_conductor_bound q hq (1 - β) (sub_pos.mpr hβ1)).trans
    (quadraticProduct_residue_lower_bound_at_cutoff_of_nonpos
      χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hsq₁ hsq₂ β hβ hβ1 hF)

end TwinPrime.Analytic
