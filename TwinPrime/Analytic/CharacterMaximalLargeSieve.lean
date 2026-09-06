import TwinPrime.Analytic.CharacterBilinear
import TwinPrime.Analytic.DyadicMaximal
import TwinPrime.Analytic.DyadicIntervalCover

/-!
# Independently selected character endpoints in the large sieve

The fixed-interval large sieve controls the binary tree of interval sums.
Its dyadic maximal inequality then permits a different prefix endpoint for
every primitive character. No maximal estimate is assumed.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The finite family of primitive characters at all positive levels up to Q. -/
def primitiveCharacterFamily (Q : ℕ) : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Icc 1 Q).sigma fun q =>
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)

def primitiveCharacterWeight (p : Σ q : ℕ, DirichletCharacter ℂ q) : ℝ :=
  (p.1 : ℝ) / Nat.totient p.1

theorem primitiveCharacterWeight_nonneg (p : Σ q : ℕ, DirichletCharacter ℂ q) :
    0 ≤ primitiveCharacterWeight p := by unfold primitiveCharacterWeight; positivity

/-- The existing fixed-interval theorem in the finite-family form needed
by the generic dyadic estimate. -/
theorem primitiveCharacterFamily_interval_bound (Q : ℕ) (a : ℕ → ℂ) (u v : ℕ) :
    (∑ p ∈ primitiveCharacterFamily Q, primitiveCharacterWeight p *
      ‖∑ n ∈ Ico u v, a n * p.2 n‖ ^ 2) ≤
      (((v - u : ℕ) : ℝ) + (Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1))) *
        ∑ n ∈ Ico u v, ‖a n‖ ^ 2 := by
  simpa only [primitiveCharacterFamily, primitiveCharacterWeight, sum_sigma, ← mul_sum,
    characterLargeSieveConstant] using primitive_character_large_sieve_log_direct Q u v a

/-- The complete dyadic tree of twisted sums has only a depth loss. -/
theorem primitive_character_dyadic_energy_le (Q M k : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        dyadicEnergy (fun n => a n * χ n) M k)) ≤
      ((k : ℝ) + 1) * characterLargeSieveConstant Q M (M + 2 ^ k) *
        ∑ n ∈ Ico M (M + 2 ^ k), ‖a n‖ ^ 2 := by
  have h := sum_weighted_dyadicEnergy_le (primitiveCharacterFamily Q)
    primitiveCharacterWeight (fun p n => a n * p.2 n) (fun n => ‖a n‖ ^ 2)
    ((Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1)))
    (fun n => sq_nonneg _) (primitiveCharacterFamily_interval_bound Q a) M k
  simpa only [primitiveCharacterFamily, primitiveCharacterWeight, sum_sigma, ← mul_sum,
    characterLargeSieveConstant, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The largest squared prefix norm in a padded dyadic interval. -/
def characterPrefixMaxSq {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (M k : ℕ) : ℝ :=
  (Icc M (M + 2 ^ k)).sup' ⟨M, mem_Icc.mpr ⟨le_rfl, Nat.le_add_right _ _⟩⟩
    (fun t => ‖∑ n ∈ Ico M t, a n * χ n‖ ^ 2)

/-- A proved maximal large sieve in endpoint-selection form. Each character
may choose its own endpoint anywhere in the same padded dyadic interval. -/
theorem primitive_character_large_sieve_selected_endpoints (Q M k : ℕ) (a : ℕ → ℂ)
    (t : (q : ℕ) → DirichletCharacter ℂ q → ℕ)
    (ht : ∀ q ∈ Icc 1 Q, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      M ≤ t q χ ∧ t q χ ≤ M + 2 ^ k) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ico M (t q χ), a n * χ n‖ ^ 2)) ≤
      ((k : ℝ) + 1) ^ 2 * characterLargeSieveConstant Q M (M + 2 ^ k) *
        ∑ n ∈ Ico M (M + 2 ^ k), ‖a n‖ ^ 2 := by
  have ht' : ∀ p ∈ primitiveCharacterFamily Q, M ≤ t p.1 p.2 ∧ t p.1 p.2 ≤ M + 2 ^ k := by
    intro p hp
    have hs := mem_sigma.mp hp
    exact ht p.1 hs.1 p.2 (mem_filter.mp hs.2).2
  have h := sum_weighted_prefix_sq_le (primitiveCharacterFamily Q) primitiveCharacterWeight
    (fun p _ => primitiveCharacterWeight_nonneg p) (fun p n => a n * p.2 n)
    (fun n => ‖a n‖ ^ 2) ((Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1)))
    (fun n => sq_nonneg _) (primitiveCharacterFamily_interval_bound Q a)
    M k (fun p => t p.1 p.2) ht'
  simpa only [primitiveCharacterFamily, primitiveCharacterWeight, sum_sigma, ← mul_sum,
    characterLargeSieveConstant, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The maximal second-moment estimate, with the finite maximum inside
the character sum. It follows by choosing an actual maximizing endpoint. -/
theorem primitive_character_maximal_large_sieve (Q M k : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterPrefixMaxSq χ a M k)) ≤
      ((k : ℝ) + 1) ^ 2 * characterLargeSieveConstant Q M (M + 2 ^ k) *
        ∑ n ∈ Ico M (M + 2 ^ k), ‖a n‖ ^ 2 := by
  have hmax (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ∃ t ∈ Icc M (M + 2 ^ k), characterPrefixMaxSq χ a M k =
        ‖∑ n ∈ Ico M t, a n * χ n‖ ^ 2 :=
    Finset.exists_mem_eq_sup' ⟨M, mem_Icc.mpr ⟨le_rfl, Nat.le_add_right _ _⟩⟩ _
  choose t ht heq using hmax
  have h := primitive_character_large_sieve_selected_endpoints Q M k a t
    (fun q _ χ _ => mem_Icc.mp (ht q χ))
  simpa only [heq] using h

/-- A finite disjoint interval family may be selected separately for every
primitive character. No factor for the number of selected intervals appears. -/
theorem primitive_character_disjoint_intervals_large_sieve {κ : Type*}
    (Q M k : ℕ) (a : ℕ → ℂ)
    (J : (q : ℕ) → DirichletCharacter ℂ q → Finset κ)
    (u v : (q : ℕ) → DirichletCharacter ℂ q → κ → ℕ)
    (hvalid : ∀ q ∈ Icc 1 Q, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ j ∈ J q χ, M ≤ u q χ j ∧ u q χ j ≤ v q χ j ∧ v q χ j ≤ M + 2 ^ k)
    (hdis : ∀ q ∈ Icc 1 Q, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ j ∈ J q χ, ∀ j' ∈ J q χ, j ≠ j' →
        Disjoint (Ico (u q χ j) (v q χ j)) (Ico (u q χ j') (v q χ j'))) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ∑ j ∈ J q χ, ‖∑ n ∈ Ico (u q χ j) (v q χ j), a n * χ n‖ ^ 2)) ≤
      (2 * ((k : ℝ) + 1) ^ 2) * characterLargeSieveConstant Q M (M + 2 ^ k) *
        ∑ n ∈ Ico M (M + 2 ^ k), ‖a n‖ ^ 2 := by
  have hv : ∀ p ∈ primitiveCharacterFamily Q, ∀ j ∈ J p.1 p.2,
      M ≤ u p.1 p.2 j ∧ u p.1 p.2 j ≤ v p.1 p.2 j ∧ v p.1 p.2 j ≤ M + 2 ^ k := by
    intro p hp
    have hs := mem_sigma.mp hp
    exact hvalid p.1 hs.1 p.2 (mem_filter.mp hs.2).2
  have hd : ∀ p ∈ primitiveCharacterFamily Q, ∀ j ∈ J p.1 p.2, ∀ j' ∈ J p.1 p.2, j ≠ j' →
      Disjoint (Ico (u p.1 p.2 j) (v p.1 p.2 j)) (Ico (u p.1 p.2 j') (v p.1 p.2 j')) := by
    intro p hp
    have hs := mem_sigma.mp hp
    exact hdis p.1 hs.1 p.2 (mem_filter.mp hs.2).2
  have h := sum_weighted_disjoint_intervals_sq_le (primitiveCharacterFamily Q)
    (fun p => J p.1 p.2) (fun p => u p.1 p.2) (fun p => v p.1 p.2)
    primitiveCharacterWeight (fun p _ => primitiveCharacterWeight_nonneg p)
    (fun p n => a n * p.2 n) (fun n => ‖a n‖ ^ 2)
    ((Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1))) (fun n => sq_nonneg _)
    (primitiveCharacterFamily_interval_bound Q a) M k hv hd
  simpa only [primitiveCharacterFamily, primitiveCharacterWeight, sum_sigma, ← mul_sum,
    characterLargeSieveConstant, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using h

end TwinPrime.Analytic
