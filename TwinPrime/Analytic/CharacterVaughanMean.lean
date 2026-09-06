import TwinPrime.Analytic.CharacterVaughanDyadic
import TwinPrime.Analytic.CharacterVaughanBox

/-!
# A finite maximal mean estimate for Vaughan's Type II term

The exact dyadic partition reduces the full finite endpoint maximum to
active box maxima. The box estimates and the two finite depth budgets
give the fourth power of the dyadic depth. This is a bound for the Type II
term; it does not supply the remaining terms of a full Vaughan mean value.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The full finite Type II maximal mean, with explicit depth and half-cutoff factors.
The maximum is inside the primitive-character sum. Only the two lower
cutoffs are required to be positive; `Q=0` and `T=0,1` are included. -/
theorem primitive_character_vaughanII_maximal_le (Q U V T : ℕ)
    (hU : 0 < U) (hV : 0 < V) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanIIMax U V T χ)) ≤
      2 * (dyadicNatDepth T : ℝ) ^ 4 * Real.log (T : ℝ) * characterLargeSieveLogFactor Q *
        ((T : ℝ) + (Q : ℝ) * T *
          (1 / Real.sqrt ((U : ℝ) / 2) + 1 / Real.sqrt ((V : ℝ) / 2)) +
            (Q : ℝ) ^ 2 * Real.sqrt (T : ℝ)) := by
  let D : ℝ := dyadicNatDepth T
  let P : ℝ := (T : ℝ) + (Q : ℝ) * T *
    (1 / Real.sqrt ((U : ℝ) / 2) + 1 / Real.sqrt ((V : ℝ) / 2)) +
      (Q : ℝ) ^ 2 * Real.sqrt (T : ℝ)
  let L : ℝ := Real.log (T : ℝ) * characterLargeSieveLogFactor Q * P
  let B (p : ℕ × ℕ) (q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
    characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
      (2 ^ p.1) (2 ^ p.2) p.1 p.2 T
  have hU0 : 0 < (U : ℝ) / 2 := by positivity
  have hV0 : 0 < (V : ℝ) / 2 := by positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hlog := Real.log_natCast_nonneg T
  have hfac : 0 ≤ characterLargeSieveLogFactor Q :=
    zero_le_one.trans (one_le_characterLargeSieveLogFactor Q)
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hlog hfac) hP
  have hbox (p : ℕ × ℕ) (hp : p ∈ activeVaughanBoxes U V T) :
      (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          B p q χ)) ≤ 2 * D ^ 2 * L := by
    have hb := activeVaughanBoxes_bounds U V T p.1 p.2 hp
    have hdepth : ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) ≤ D ^ 2 := by
      dsimp [D]
      exact_mod_cast activeVaughanBoxes_depth_product_le U V T p.1 p.2 hp
    have hpoly := primitive_character_vaughan_box_polynomial_le Q U V T p.1 p.2
      ((U : ℝ) / 2) ((V : ℝ) / 2) hU0 hb.1 hV0 hb.2.1 hb.2.2.1
    calc
      _ ≤ (2 * ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) *
          Real.log (T : ℝ) * characterLargeSieveLogFactor Q * P := by
        simpa only [B, P] using hpoly
      _ = (2 * (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1))) * L := by dsimp [L]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdepth (by norm_num)) hL
  have hcard : ((activeVaughanBoxes U V T).card : ℝ) ≤ D ^ 2 := by
    dsimp [D]
    exact_mod_cast card_activeVaughanBoxes_le U V T
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
        (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∑ p ∈ activeVaughanBoxes U V T, B p q χ) := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro χ _
      exact characterVaughanIIMax_le_active_max U V T χ
    _ = ∑ q ∈ Icc 1 Q, ∑ p ∈ activeVaughanBoxes U V T,
        (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            B p q χ) := by
      apply sum_congr rfl
      intro q _
      rw [sum_comm, mul_sum]
    _ = ∑ p ∈ activeVaughanBoxes U V T, ∑ q ∈ Icc 1 Q,
        (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            B p q χ) := by rw [sum_comm]
    _ ≤ ∑ _ ∈ activeVaughanBoxes U V T, 2 * D ^ 2 * L := sum_le_sum hbox
    _ = ((activeVaughanBoxes U V T).card : ℝ) * (2 * D ^ 2 * L) := by simp
    _ ≤ D ^ 2 * (2 * D ^ 2 * L) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by dsimp [D, L, P]; ring

/-- The same full Type II estimate in the inverse-character convention. -/
theorem primitive_character_vaughanII_maximal_inv_le (Q U V T : ℕ)
    (hU : 0 < U) (hV : 0 < V) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanIIMax U V T χ⁻¹)) ≤
      2 * (dyadicNatDepth T : ℝ) ^ 4 * Real.log (T : ℝ) * characterLargeSieveLogFactor Q *
        ((T : ℝ) + (Q : ℝ) * T *
          (1 / Real.sqrt ((U : ℝ) / 2) + 1 / Real.sqrt ((V : ℝ) / 2)) +
            (Q : ℝ) ^ 2 * Real.sqrt (T : ℝ)) := by
  have heq (q : ℕ) := sum_primitive_character_inv_eq q (characterVaughanIIMax U V T)
  simp_rw [heq]
  exact primitive_character_vaughanII_maximal_le Q U V T hU hV

end TwinPrime.Analytic
