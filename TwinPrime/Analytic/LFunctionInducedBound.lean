import TwinPrime.Analytic.LFunctionZeroInequality
import TwinPrime.Analytic.LFunctionEulerCorrection

/-!

# One-sided logarithmic-derivative bounds for induced characters

Every nonprincipal character is compared to its actual primitive inducing
character. The finite Euler correction adds at most the logarithm of the
original modulus. For principal characters the zeta term is retained.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- No primitivity is assumed for the original character. -/
theorem neg_logDerivative_LFunction_re_le_budget_add_log {q : ℕ} [NeZero q]
    (η : DirichletCharacter ℂ q) (hη : η ≠ 1)
    (σ t : ℝ) (hσ : 1 < σ) (hσu : σ ≤ 9 / 8) :
    (-deriv (DirichletCharacter.LFunction η) ((σ : ℂ) + Complex.I * t) /
      DirichletCharacter.LFunction η ((σ : ℂ) + Complex.I * t)).re ≤
        primitiveLFunctionLogBudget q t + Real.log q := by
  letI : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
  have hd : 1 < η.conductor := by
    have hd0 := η.conductor_ne_zero
    have hd1 : η.conductor ≠ 1 := fun h => hη
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
    omega
  have hdq : η.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) η.conductor_dvd_level
  let s : ℂ := (σ : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simpa [s] using hσ
  have hp := neg_logDerivative_LFunction_re_le_budget hd η.primitiveCharacter
    η.primitiveCharacter_isPrimitive σ t hσ hσu
  have hK := primitiveLFunctionLogBudget_mono_conductor η.conductor q hd.le hdq t
  have he := norm_logDerivative_LFunction_sub_primitiveCharacter_le η s hs
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (deriv (DirichletCharacter.LFunction η) s / DirichletCharacter.LFunction η s -
      deriv (DirichletCharacter.LFunction η.primitiveCharacter) s /
        DirichletCharacter.LFunction η.primitiveCharacter s))).1
  simp only [Complex.sub_re] at hr
  change (-deriv (DirichletCharacter.LFunction η.primitiveCharacter) s /
    DirichletCharacter.LFunction η.primitiveCharacter s).re ≤
      primitiveLFunctionLogBudget η.conductor t at hp
  change (-deriv (DirichletCharacter.LFunction η) s /
    DirichletCharacter.LFunction η s).re ≤ _
  rw [neg_div, Complex.neg_re] at hp ⊢
  linarith

/-- A principal character retains the complete zeta logarithmic derivative;
its missing Euler factors occur with the opposite correction sign. -/
theorem neg_logDerivative_LFunction_principal_eq_zeta_sub_correction
    (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
      -deriv riemannZeta s / riemannZeta s -
        characterEulerCorrection (1 : DirichletCharacter ℂ 1) q s := by
  simpa only [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq] using
    neg_logDerivative_LFunction_changeLevel (Nat.one_dvd q)
      (1 : DirichletCharacter ℂ 1) s hs

/-- The principal inducing correction also costs at most `log q` in real part. -/
theorem neg_logDerivative_LFunction_principal_re_le_zeta_add_log
    (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s).re ≤
      (-deriv riemannZeta s / riemannZeta s).re + Real.log q := by
  rw [neg_logDerivative_LFunction_principal_eq_zeta_sub_correction q s hs, Complex.sub_re]
  have he := norm_characterEulerCorrection_le_log (1 : DirichletCharacter ℂ 1)
    q (NeZero.pos q) s hs.le
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (characterEulerCorrection (1 : DirichletCharacter ℂ 1) q s))).1
  linarith

end TwinPrime.Analytic
