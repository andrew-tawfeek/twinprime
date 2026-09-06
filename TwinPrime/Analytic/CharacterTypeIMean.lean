import TwinPrime.Analytic.CharacterTypeIBounds
import TwinPrime.Analytic.PrimitiveCharacterCounting
import TwinPrime.Analytic.CharacterVaughanMean

/-!
# Finite Vaughan first moments for primitive characters

Exact character counts and the primitive interval bounds control the two
Type I maxima over moduli at least two. The low term has a constant budget.
Modulus one is bounded separately by `T log T`. Combining these bounds with
the proved Type II mean gives an explicit uncentered character mean value.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

theorem primitive_character_vaughanI1_maximal_mean_le (R U T : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanI1Max U T χ)) ≤
      2 * (U : ℝ) * (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) * Real.log T := by
  have hT := Real.log_natCast_nonneg T
  have h := sum_weighted_primitive_le_sum_budget R (fun _ χ => characterVaughanI1Max U T χ)
    (fun q => 2 * (U : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log T)
    (fun q _ => by have := Real.log_natCast_nonneg q; positivity)
    (fun q hq χ hχ => characterVaughanI1Max_le
      (by have := (mem_Icc.mp hq).1; omega) U T χ hχ)
  calc
    _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) *
        (2 * (U : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log T) := h
    _ = (2 * (U : ℝ) * Real.log T) *
        (∑ q ∈ Icc 2 R, (q : ℝ) * Real.sqrt q * (1 + Real.log q)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (2 * (U : ℝ) * Real.log T) *
        ((R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left (sum_modulus_sqrt_log_le R) (by positivity)
    _ = _ := by ring

theorem primitive_character_vaughanI2_maximal_mean_le (R U V T : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanI2Max U V T χ)) ≤
      ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) *
        (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) := by
  have hUV := Real.log_natCast_nonneg (U * V)
  have h := sum_weighted_primitive_le_sum_budget R (fun _ χ => characterVaughanI2Max U V T χ)
    (fun q => ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) * Real.sqrt q * (1 + Real.log q))
    (fun q _ => by have := Real.log_natCast_nonneg q; positivity)
    (fun q hq χ hχ => characterVaughanI2Max_le
      (by have := (mem_Icc.mp hq).1; omega) U V T χ hχ)
  calc
    _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) *
        (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) * Real.sqrt q * (1 + Real.log q)) := h
    _ = (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ)) *
        (∑ q ∈ Icc 2 R, (q : ℝ) * Real.sqrt q * (1 + Real.log q)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ)) *
        ((R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left (sum_modulus_sqrt_log_le R) (by positivity)
    _ = _ := by ring

/-- The low von Mangoldt term's common budget, averaged over primitive characters. -/
theorem primitive_character_low_mean_le (R V : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        (V : ℝ) * Real.log V)) ≤ (V : ℝ) * Real.log V * (R : ℝ) ^ 2 := by
  have hV := Real.log_natCast_nonneg V
  have h := sum_weighted_primitive_le_const R (fun _ _ => (V : ℝ) * Real.log V)
    ((V : ℝ) * Real.log V) (by positivity) (fun _ _ _ _ => le_rfl)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- Separate the positive-modulus interval at one, including the empty range. -/
theorem sum_Icc_one_le_first_add_sum_Icc_two (R : ℕ) (f : ℕ → ℝ) (hf : 0 ≤ f 1) :
    (∑ q ∈ Icc 1 R, f q) ≤ f 1 + ∑ q ∈ Icc 2 R, f q := by
  by_cases hR : R = 0
  · subst R
    simpa using hf
  · have hI : Icc 1 R = insert 1 (Icc 2 R) := by
      ext q
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]

/-- An explicit finite mean for the uncentered prime character maximum.
Modulus one is treated by the elementary bound; the other moduli use the
two Type I estimates and the actual Type II maximal mean. -/
theorem primitive_characterPsiMax_mean_le (R U V T : ℕ) (hU : 0 < U) (hV : 0 < V) :
    (∑ q ∈ Icc 1 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterPsiMax T χ)) ≤
      (T : ℝ) * Real.log T +
      2 * (U : ℝ) * (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) * Real.log T +
      ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) *
        (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) +
      (V : ℝ) * Real.log V * (R : ℝ) ^ 2 +
      2 * (dyadicNatDepth T : ℝ) ^ 4 * Real.log T * characterLargeSieveLogFactor R *
        ((T : ℝ) + (R : ℝ) * T *
          (1 / Real.sqrt ((U : ℝ) / 2) + 1 / Real.sqrt ((V : ℝ) / 2)) +
            (R : ℝ) ^ 2 * Real.sqrt T) := by
  let F (q : ℕ) : ℝ := (q : ℝ) / Nat.totient q *
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), characterPsiMax T χ
  let A1 : ℝ := 2 * (U : ℝ) * (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) * Real.log T
  let A2 : ℝ := ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) *
    (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R)
  let A0 : ℝ := (V : ℝ) * Real.log V * (R : ℝ) ^ 2
  let AII : ℝ := 2 * (dyadicNatDepth T : ℝ) ^ 4 * Real.log T * characterLargeSieveLogFactor R *
    ((T : ℝ) + (R : ℝ) * T *
      (1 / Real.sqrt ((U : ℝ) / 2) + 1 / Real.sqrt ((V : ℝ) / 2)) +
        (R : ℝ) ^ 2 * Real.sqrt T)
  have hF1 : 0 ≤ F 1 := mul_nonneg (by positivity)
    (sum_nonneg fun χ _ => characterPsiMax_nonneg T χ)
  have hlogT := Real.log_natCast_nonneg T
  have h1 : F 1 ≤ (T : ℝ) * Real.log T := by
    simpa only [F, Nat.cast_one, one_mul] using weighted_sum_primitive_le 1 (by decide)
      (characterPsiMax T) ((T : ℝ) * Real.log T) (by positivity)
      (fun χ _ => characterPsiMax_le T χ)
  have hII : (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanIIMax U V T χ)) ≤ AII := by
    calc
      _ ≤ ∑ q ∈ Icc 1 R, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            characterVaughanIIMax U V T χ) := by
        apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by omega) le_rfl)
        intro q _ _
        exact mul_nonneg (by positivity) (sum_nonneg fun χ _ => characterVaughanIIMax_nonneg U V T χ)
      _ ≤ _ := primitive_character_vaughanII_maximal_le R U V T hU hV
  have hrest : (∑ q ∈ Icc 2 R, F q) ≤ A1 + A2 + A0 + AII := by
    calc
      _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            (characterVaughanI1Max U T χ + characterVaughanI2Max U V T χ +
              (V : ℝ) * Real.log V + characterVaughanIIMax U V T χ)) := by
        apply sum_le_sum
        intro q _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun χ _ => characterPsiMax_le_vaughan U V T χ
      _ = (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            characterVaughanI1Max U T χ)) +
          (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            characterVaughanI2Max U V T χ)) +
          (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
          (∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            (V : ℝ) * Real.log V)) +
          (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            characterVaughanIIMax U V T χ)) := by simp only [sum_add_distrib, mul_add]
      _ ≤ _ := add_le_add
        (add_le_add (add_le_add (primitive_character_vaughanI1_maximal_mean_le R U T)
          (primitive_character_vaughanI2_maximal_mean_le R U V T))
          (primitive_character_low_mean_le R V)) hII
  calc
    _ ≤ F 1 + ∑ q ∈ Icc 2 R, F q := sum_Icc_one_le_first_add_sum_Icc_two R F hF1
    _ ≤ (T : ℝ) * Real.log T + (A1 + A2 + A0 + AII) := add_le_add h1 hrest
    _ = _ := by dsimp [A1, A2, A0, AII]; ring

end TwinPrime.Analytic
