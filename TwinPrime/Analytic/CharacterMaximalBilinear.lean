import TwinPrime.Analytic.DyadicStaircaseFirstMoment
import TwinPrime.Analytic.CharacterMaximalLargeSieve

/-!
# Maximal product-cutoff primitive-character bilinear sums

The exact clamped staircase identity and the proved fixed-interval large
sieve give a bilinear first moment on a dyadic box. Every character may
select its own natural product cutoff. Selecting actual finite maximizers
then puts the maximum inside the primitive-character sum.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- A character-twisted bilinear sum on a dyadic box with the exact product cutoff. -/
def characterProductCutoffSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (M N k j t : ℕ) : ℂ :=
  ∑ m ∈ Ico M (M + 2 ^ k),
    ∑ n ∈ Ico N (N + 2 ^ j) with m * n ≤ t, a m * b n * χ (m * n)

/-- Multiplicativity and the exact filtered-row identity give a staircase.
Only the first coordinate's starting point needs to be positive. -/
theorem characterProductCutoffSum_eq_staircase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (M N k j t : ℕ) (hM : 0 < M) :
    characterProductCutoffSum χ a b M N k j t =
      ∑ m ∈ Ico M (M + 2 ^ k), (a m * χ m) *
        ∑ n ∈ Ico N (productCutoffBoundary t N (2 ^ j) m), b n * χ n := by
  unfold characterProductCutoffSum
  apply sum_congr rfl
  intro m hm
  rw [filter_Ico_productCutoff_eq t N (2 ^ j) m (hM.trans_le (mem_Ico.mp hm).1), mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [map_mul]
  ring

/-- The full baseline and internal-node decomposition of the twisted sum. -/
theorem characterProductCutoffSum_eq_baseline_add_detail {q : ℕ}
    (χ : DirichletCharacter ℂ q) (a b : ℕ → ℂ) (M N k j t : ℕ) (hM : 0 < M) :
    characterProductCutoffSum χ a b M N k j t =
      (∑ m ∈ Ico M (M + 2 ^ k), a m * χ m) *
        (∑ n ∈ Ico N (productCutoffBoundary t N (2 ^ j) (M + 2 ^ k - 1)), b n * χ n) +
          dyadicStaircaseDetail (fun m => a m * χ m) (fun n => b n * χ n)
            (productCutoffBoundary t N (2 ^ j)) M k := by
  rw [characterProductCutoffSum_eq_staircase χ a b M N k j t hM]
  exact sum_dyadic_staircase_eq (fun m => a m * χ m) (fun n => b n * χ n)
    (productCutoffBoundary t N (2 ^ j)) M N k
    (fun m _ => le_productCutoffBoundary t N (2 ^ j) m)
    (productCutoffBoundary_antitoneOn t N (2 ^ j) M (M + 2 ^ k) hM)

/-- A different product cutoff may be selected for every primitive character.
There is no restriction on how the endpoints depend on the characters. -/
theorem primitive_character_bilinear_selected_endpoints (Q M N k j : ℕ)
    (a b : ℕ → ℂ) (hM : 0 < M)
    (t : (q : ℕ) → DirichletCharacter ℂ q → ℕ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖characterProductCutoffSum χ a b M N k j (t q χ)‖)) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) *
        Real.sqrt (characterLargeSieveConstant Q M (M + 2 ^ k) *
          ∑ m ∈ Ico M (M + 2 ^ k), ‖a m‖ ^ 2) *
        Real.sqrt (characterLargeSieveConstant Q N (N + 2 ^ j) *
          ∑ n ∈ Ico N (N + 2 ^ j), ‖b n‖ ^ 2) := by
  have hC : 0 ≤ (Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1)) := by
    have hlog : 0 ≤ Real.log ((Q : ℝ) + 1) :=
      Real.log_nonneg (by have : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q; linarith)
    positivity
  have h := sum_weighted_dyadic_staircase_le (primitiveCharacterFamily Q)
    primitiveCharacterWeight (fun p _ => primitiveCharacterWeight_nonneg p)
    (fun p n => a n * p.2 n) (fun p n => b n * p.2 n)
    (fun n => ‖a n‖ ^ 2) (fun n => ‖b n‖ ^ 2)
    ((Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1))) hC
    (fun n => sq_nonneg _) (fun n => sq_nonneg _)
    (primitiveCharacterFamily_interval_bound Q a) (primitiveCharacterFamily_interval_bound Q b)
    M N k j (fun p => productCutoffBoundary (t p.1 p.2) N (2 ^ j))
    (fun p _ => productCutoffBoundary_antitoneOn (t p.1 p.2) N (2 ^ j) M (M + 2 ^ k) hM)
    (fun p _ m _ => ⟨le_productCutoffBoundary (t p.1 p.2) N (2 ^ j) m,
      productCutoffBoundary_le (t p.1 p.2) N (2 ^ j) m⟩)
  simp_rw [characterProductCutoffSum_eq_staircase _ a b M N k j _ hM]
  simpa only [primitiveCharacterFamily, primitiveCharacterWeight, sum_sigma, ← mul_sum,
    characterLargeSieveConstant, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The maximum norm over the finite endpoint set `0 ≤ t ≤ T`. -/
def characterProductCutoffMax {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) (M N k j T : ℕ) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterProductCutoffSum χ a b M N k j t‖)

/-- The bilinear first moment with the finite maximum inside the character sum. -/
theorem primitive_character_maximal_bilinear (Q M N k j T : ℕ)
    (a b : ℕ → ℂ) (hM : 0 < M) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterProductCutoffMax χ a b M N k j T)) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) *
        Real.sqrt (characterLargeSieveConstant Q M (M + 2 ^ k) *
          ∑ m ∈ Ico M (M + 2 ^ k), ‖a m‖ ^ 2) *
        Real.sqrt (characterLargeSieveConstant Q N (N + 2 ^ j) *
          ∑ n ∈ Ico N (N + 2 ^ j), ‖b n‖ ^ 2) := by
  have hmax (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ∃ t ∈ Icc 0 T, characterProductCutoffMax χ a b M N k j T =
        ‖characterProductCutoffSum χ a b M N k j t‖ :=
    Finset.exists_mem_eq_sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩ _
  choose t _ heq using hmax
  have h := primitive_character_bilinear_selected_endpoints Q M N k j a b hM t
  simpa only [heq] using h

/-- Inverting all primitive characters preserves the finite maximal sum. -/
theorem primitive_character_maximal_bilinear_inv (Q M N k j T : ℕ)
    (a b : ℕ → ℂ) (hM : 0 < M) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterProductCutoffMax χ⁻¹ a b M N k j T)) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) *
        Real.sqrt (characterLargeSieveConstant Q M (M + 2 ^ k) *
          ∑ m ∈ Ico M (M + 2 ^ k), ‖a m‖ ^ 2) *
        Real.sqrt (characterLargeSieveConstant Q N (N + 2 ^ j) *
          ∑ n ∈ Ico N (N + 2 ^ j), ‖b n‖ ^ 2) := by
  have heq (q : ℕ) := sum_primitive_character_inv_eq q
    (fun χ => characterProductCutoffMax χ a b M N k j T)
  simp_rw [heq]
  exact primitive_character_maximal_bilinear Q M N k j T a b hM

end TwinPrime.Analytic
