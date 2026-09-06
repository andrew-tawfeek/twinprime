import TwinPrime.Analytic.CharacterMaximalBilinear
import TwinPrime.Analytic.VaughanBoxCoefficients
import TwinPrime.Analytic.BilinearBoxPolynomial

/-!
# A maximal primitive-character estimate for one Vaughan box

The masked Möbius and divisor coefficients are inserted into the proved
maximal bilinear theorem. Their energies give the box polynomial, which
can then be bounded using real lower bounds on the two side lengths.
The natural masking cutoffs and these real comparison bounds are separate.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The logarithmic factor in the proved primitive-character large sieve. -/
def characterLargeSieveLogFactor (Q : ℕ) : ℝ := 1 + 2 * Real.log ((Q : ℝ) + 1)

/-- The part of the large-sieve constant independent of interval length. -/
def characterLargeSieveOffset (Q : ℕ) : ℝ := (Q : ℝ) ^ 2 * characterLargeSieveLogFactor Q

theorem one_le_characterLargeSieveLogFactor (Q : ℕ) : 1 ≤ characterLargeSieveLogFactor Q := by
  have hlog : 0 ≤ Real.log ((Q : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q; linarith)
  unfold characterLargeSieveLogFactor
  linarith

theorem characterLargeSieveOffset_nonneg (Q : ℕ) : 0 ≤ characterLargeSieveOffset Q :=
  mul_nonneg (sq_nonneg _) (zero_le_one.trans (one_le_characterLargeSieveLogFactor Q))

theorem characterLargeSieveConstant_dyadic (Q M k : ℕ) :
    characterLargeSieveConstant Q M (M + 2 ^ k) = (2 : ℝ) ^ k + characterLargeSieveOffset Q := by
  simp [characterLargeSieveConstant, characterLargeSieveOffset, characterLargeSieveLogFactor]

/-- Extract the nonnegative logarithmic coefficient from the two square roots. -/
theorem sqrt_box_energy_mul_eq (M N C L : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    Real.sqrt ((M + C) * M) * Real.sqrt ((N + C) * (N * L ^ 2)) =
      L * Real.sqrt (M * N * (M + C) * (N + C)) := by
  rw [← Real.sqrt_mul (mul_nonneg (add_nonneg hM hC) hM)]
  have heq : ((M + C) * M) * ((N + C) * (N * L ^ 2)) =
      L ^ 2 * (M * N * (M + C) * (N + C)) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

/-- The maximal first moment on a global dyadic box, with the actual Vaughan masks. -/
theorem primitive_character_vaughan_box_maximal_le (Q U V T k j : ℕ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
          (2 ^ k) (2 ^ j) k j T)) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) * Real.log (T : ℝ) *
        Real.sqrt ((2 : ℝ) ^ k * (2 : ℝ) ^ j *
          ((2 : ℝ) ^ k + characterLargeSieveOffset Q) *
          ((2 : ℝ) ^ j + characterLargeSieveOffset Q)) := by
  have hC := characterLargeSieveOffset_nonneg Q
  have hL := Real.log_natCast_nonneg T
  have hmax := primitive_character_maximal_bilinear Q (2 ^ k) (2 ^ j) k j T
    (vaughanBoxA U T) (vaughanBoxB V T) (by positivity)
  rw [characterLargeSieveConstant_dyadic, characterLargeSieveConstant_dyadic] at hmax
  have hA := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (sum_norm_vaughanBoxA_sq_Ico_le U T (2 ^ k) k)
    (show 0 ≤ (2 : ℝ) ^ k + characterLargeSieveOffset Q by positivity))
  have hB := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (sum_norm_vaughanBoxB_sq_Ico_le V T (2 ^ j) j)
    (show 0 ≤ (2 : ℝ) ^ j + characterLargeSieveOffset Q by positivity))
  calc
    _ ≤ (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) *
        Real.sqrt (((2 : ℝ) ^ k + characterLargeSieveOffset Q) *
          ∑ m ∈ Ico (2 ^ k) (2 ^ k + 2 ^ k), ‖vaughanBoxA U T m‖ ^ 2) *
        Real.sqrt (((2 : ℝ) ^ j + characterLargeSieveOffset Q) *
          ∑ n ∈ Ico (2 ^ j) (2 ^ j + 2 ^ j), ‖vaughanBoxB V T n‖ ^ 2) := hmax
    _ ≤ (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) *
        Real.sqrt (((2 : ℝ) ^ k + characterLargeSieveOffset Q) * (2 : ℝ) ^ k) *
        Real.sqrt (((2 : ℝ) ^ j + characterLargeSieveOffset Q) *
          ((2 : ℝ) ^ j * (Real.log (T : ℝ)) ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hB
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_assoc, sqrt_box_energy_mul_eq _ _ _ _ (by positivity) hC hL]
      ring

/-- The polynomial specialization uses real lower side bounds, independently
of the natural cutoffs in the masks. -/
theorem primitive_character_vaughan_box_polynomial_le (Q U V T k j : ℕ)
    (U0 V0 : ℝ) (hU0 : 0 < U0) (hUk : U0 ≤ (2 : ℝ) ^ k)
    (hV0 : 0 < V0) (hVj : V0 ≤ (2 : ℝ) ^ j)
    (hprod : (2 : ℝ) ^ k * (2 : ℝ) ^ j ≤ (T : ℝ)) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
          (2 ^ k) (2 ^ j) k j T)) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) * Real.log (T : ℝ) *
        characterLargeSieveLogFactor Q *
          ((T : ℝ) + (Q : ℝ) * T * (1 / Real.sqrt U0 + 1 / Real.sqrt V0) +
            (Q : ℝ) ^ 2 * Real.sqrt (T : ℝ)) := by
  have hp := bilinear_box_polynomial_le_log_factor ((2 : ℝ) ^ k) ((2 : ℝ) ^ j)
    U0 V0 T Q (characterLargeSieveLogFactor Q) hU0 hUk hV0 hVj hprod
    (Nat.cast_nonneg Q) (one_le_characterLargeSieveLogFactor Q)
  have hL := Real.log_natCast_nonneg T
  apply (primitive_character_vaughan_box_maximal_le Q U V T k j).trans
  simpa only [characterLargeSieveOffset, mul_assoc] using
    mul_le_mul_of_nonneg_left hp (show 0 ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) * Real.log (T : ℝ) by positivity)

end TwinPrime.Analytic
