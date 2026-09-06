import TwinPrime.Analytic.CharacterTypeIMean
import TwinPrime.Analytic.VaughanMeanParameters
import TwinPrime.Analytic.ConductorMean
import TwinPrime.Analytic.ConductorReduction
import TwinPrime.Analytic.SmallConductorMean

/-!
# A proved primitive-character mean value and conductor tail

Eighth-root internal cutoffs turn the finite Vaughan estimates into a
six-logarithm mean bound in the required modulus range. The proved Abel
identity then controls the large-conductor tail. No character mean-value
or distribution estimate is an argument of these theorems.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The full maximal primitive-character mean value, with a power-saving
middle term and an explicit absolute constant. -/
theorem primitive_character_mean_value (T R : ℕ) (hT : 256 ≤ T)
    (hRpos : 1 ≤ R) (hR : (R : ℝ) ≤ Real.sqrt T) :
    (∑ q ∈ Icc 1 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterPsiMax T χ)) ≤
      bvMeanConstant * bvMeanPolynomial T R * (Real.log T) ^ 6 := by
  have hraw := primitive_characterPsiMax_mean_le R (bvInternalCutoff T) (bvInternalCutoff T) T
    (bvInternalCutoff_pos T hT) (bvInternalCutoff_pos T hT)
  exact hraw.trans (bvInternalCutoff_mean_budget_le T R hT hRpos hR)

/-- The inverse-character convention has the same full maximal mean. -/
theorem primitive_character_mean_value_inv (T R : ℕ) (hT : 256 ≤ T)
    (hRpos : 1 ≤ R) (hR : (R : ℝ) ≤ Real.sqrt T) :
    (∑ q ∈ Icc 1 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterPsiMax T χ⁻¹)) ≤
      bvMeanConstant * bvMeanPolynomial T R * (Real.log T) ^ 6 := by
  have heq (q : ℕ) := sum_primitive_character_inv_eq q (characterPsiMax T)
  simp_rw [heq]
  exact primitive_character_mean_value T R hT hRpos hR

/-- Explicit budget after the reciprocal-conductor Abel sum. -/
def bvLargeConductorBudget (T R₀ Q : ℕ) : ℝ :=
  bvMeanConstant * (Real.log T) ^ 6 *
    ((T : ℝ) / R₀ + (T : ℝ) ^ (15 / 16 : ℝ) * (1 + Real.log ((Q : ℝ) / R₀)) +
      2 * Real.sqrt T * Q)

/-- The actual centered primitive-conductor tail follows from the proved
mean value. Conductor one remains outside the tail. -/
theorem sum_large_primitiveCharacterMass_le (T R₀ Q : ℕ) (hT : 256 ≤ T)
    (hR₀ : 1 ≤ R₀) (hRQ : R₀ ≤ Q) (hQ : (Q : ℝ) ≤ Real.sqrt T) :
    (∑ r ∈ Ioc R₀ Q, primitiveCharacterMass T r / Nat.totient r) ≤
      bvLargeConductorBudget T R₀ Q := by
  let A := bvMeanConstant * (Real.log T) ^ 6 * T
  let B := bvMeanConstant * (Real.log T) ^ 6 * (T : ℝ) ^ (15 / 16 : ℝ)
  let D := bvMeanConstant * (Real.log T) ^ 6 * Real.sqrt T
  have hC : 0 ≤ bvMeanConstant := by unfold bvMeanConstant; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmean (r : ℕ) (hr : r ∈ Icc R₀ Q) :
      (∑ q ∈ Icc 1 r, (q : ℝ) / Nat.totient q *
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          characterPsiMax T χ)) ≤ A + B * r + D * (r : ℝ) ^ 2 := by
    have hrpos : 1 ≤ r := hR₀.trans (mem_Icc.mp hr).1
    have hrbound : (r : ℝ) ≤ Real.sqrt T :=
      (show (r : ℝ) ≤ Q by exact_mod_cast (mem_Icc.mp hr).2).trans hQ
    apply (primitive_character_mean_value T r hT hrpos hrbound).trans_eq
    dsimp [A, B, D, bvMeanPolynomial]
    ring
  have h := sum_primitiveCharacterMass_div_totient_le_of_quadratic_mean
    T R₀ Q hR₀ hRQ A B D hA hB hD hmean
  convert h using 1
  dsimp [A, B, D, bvLargeConductorBudget]
  ring

/-- The finite conductor reduction now has only the small-conductor sum
left as an unevaluated arithmetic quantity. -/
theorem sum_progressionMaxError_le_small_conductors_and_tail (T R₀ Q : ℕ)
    (hT : 256 ≤ T) (hR₀ : 1 ≤ R₀) (hRQ : R₀ ≤ Q) (hQ : (Q : ℝ) ≤ Real.sqrt T) :
    (∑ q ∈ Icc 1 Q, progressionMaxError T q) ≤
      totientReciprocalConstant * (1 + Real.log Q) *
        ((∑ r ∈ Icc 1 R₀, primitiveCharacterMass T r / Nat.totient r) +
          bvLargeConductorBudget T R₀ Q) +
        Q * (Real.log Q + 2 * Real.sqrt T * Real.log T) := by
  have hsplit : (∑ r ∈ Icc 1 Q, primitiveCharacterMass T r / Nat.totient r) =
      (∑ r ∈ Icc 1 R₀, primitiveCharacterMass T r / Nat.totient r) +
        ∑ r ∈ Ioc R₀ Q, primitiveCharacterMass T r / Nat.totient r := by
    have hI (S : ℕ) : Icc 1 S = Ioc 0 S := by
      ext r
      simp only [mem_Icc, mem_Ioc]
      omega
    simp only [hI]
    exact (sum_Ioc_consecutive (fun r => primitiveCharacterMass T r / Nat.totient r)
      (Nat.zero_le R₀) hRQ).symm
  have hfactor : 0 ≤ totientReciprocalConstant * (1 + Real.log Q) := by
    have hc := totientReciprocalConstant_nonneg
    have hl := Real.log_natCast_nonneg Q
    positivity
  have h := sum_progressionMaxError_le_weighted_conductor_sum T Q (by omega)
  rw [hsplit] at h
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (sum_large_primitiveCharacterMass_le T R₀ Q hT hR₀ hRQ hQ)) hfactor) le_rfl)

/-- The split also covers an empty large-conductor range and modulus range
zero. The small-conductor sum stops at the actual smaller endpoint. -/
theorem sum_progressionMaxError_le_small_conductors_and_tail_if (T R₀ Q : ℕ)
    (hT : 256 ≤ T) (hR₀ : 1 ≤ R₀) (hQ : (Q : ℝ) ≤ Real.sqrt T) :
    (∑ q ∈ Icc 1 Q, progressionMaxError T q) ≤
      totientReciprocalConstant * (1 + Real.log Q) *
        ((∑ r ∈ Icc 1 (min R₀ Q), primitiveCharacterMass T r / Nat.totient r) +
          if R₀ ≤ Q then bvLargeConductorBudget T R₀ Q else 0) +
        Q * (Real.log Q + 2 * Real.sqrt T * Real.log T) := by
  by_cases hRQ : R₀ ≤ Q
  · simpa only [if_pos hRQ, min_eq_left hRQ] using
      sum_progressionMaxError_le_small_conductors_and_tail T R₀ Q hT hR₀ hRQ hQ
  · have hQR : Q ≤ R₀ := by omega
    simpa only [if_neg hRQ, min_eq_right hQR, add_zero] using
      sum_progressionMaxError_le_weighted_conductor_sum T Q (by omega)

/-- An explicit uniform centered small-conductor bound is the only
distribution input in this finite progression estimate. -/
theorem sum_progressionMaxError_le_small_conductor_budget (T R₀ Q : ℕ)
    (hT : 256 ≤ T) (hR₀ : 1 ≤ R₀) (hQ : (Q : ℝ) ≤ Real.sqrt T)
    (E : ℝ) (hE : 0 ≤ E)
    (hsmall : ∀ r ∈ Icc 1 R₀, ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
      characterMaxError T χ ≤ E) :
    (∑ q ∈ Icc 1 Q, progressionMaxError T q) ≤
      totientReciprocalConstant * (1 + Real.log Q) *
        ((R₀ : ℝ) * E + if R₀ ≤ Q then bvLargeConductorBudget T R₀ Q else 0) +
        Q * (Real.log Q + 2 * Real.sqrt T * Real.log T) := by
  have hfactor : 0 ≤ totientReciprocalConstant * (1 + Real.log Q) := by
    have hc := totientReciprocalConstant_nonneg
    have hl := Real.log_natCast_nonneg Q
    positivity
  exact (sum_progressionMaxError_le_small_conductors_and_tail_if T R₀ Q hT hR₀ hQ).trans
    (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (sum_small_primitiveCharacterMass_le T R₀ Q E hE hsmall) le_rfl) hfactor) le_rfl)

end TwinPrime.Analytic
