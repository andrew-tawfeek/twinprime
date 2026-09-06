import TwinPrime.Analytic.RationalLargeSieve

/-!
# Rectangular primitive-character bilinear first moments

Multiplicativity factors a sum over two fixed intervals. Weighted finite
Cauchy--Schwarz and the proved large sieve then bound its first moment.
These statements have no product cutoff and no maximum over endpoints;
neither operation is supplied by this rectangular estimate.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The explicit constant in the logarithmic primitive-character large sieve. -/
def characterLargeSieveConstant (Q M N : ℕ) : ℝ :=
  ((N - M : ℕ) : ℝ) + (Q : ℝ) ^ 2 * (1 + 2 * Real.log ((Q : ℝ) + 1))

/-- Inversion permutes the primitive characters, including conductor one. -/
theorem sum_primitive_character_inv_eq (q : ℕ) (F : DirichletCharacter ℂ q → ℝ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      F χ⁻¹) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        F χ := by
  apply sum_bij (fun χ _ => χ⁻¹)
  · intro χ hχ
    simpa only [mem_filter, mem_univ, true_and, DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv] using hχ
  · intro χ _ ψ _ heq
    exact inv_injective heq
  · intro χ hχ
    refine ⟨χ⁻¹, ?_, inv_inv χ⟩
    simpa only [mem_filter, mem_univ, true_and, DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv] using hχ
  · intro χ _
    rfl

/-- The second moment is unchanged when all characters are inverted. -/
theorem primitive_character_second_moment_inv_eq (q : ℕ) (s : Finset ℕ)
    (a : ℕ → ℂ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖∑ n ∈ s, a n * χ⁻¹ n‖ ^ 2) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ n‖ ^ 2 :=
  sum_primitive_character_inv_eq q (fun χ => ‖∑ n ∈ s, a n * χ n‖ ^ 2)

/-- The logarithmic large sieve in the non-inverted character convention. -/
theorem primitive_character_large_sieve_log_direct (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ico M N, a n * χ n‖ ^ 2)) ≤
      characterLargeSieveConstant Q M N * ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  have h := primitive_character_large_sieve_log Q M N a
  simpa only [primitive_character_second_moment_inv_eq, characterLargeSieveConstant] using h

/-- Weighted Cauchy--Schwarz for two real sequences; zero weights are allowed. -/
theorem weighted_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι)
    (w f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i * g i) ≤
      Real.sqrt (∑ i ∈ s, w i * f i ^ 2) *
        Real.sqrt (∑ i ∈ s, w i * g i ^ 2) := by
  have hf : ∀ i ∈ s, 0 ≤ w i * f i ^ 2 :=
    fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hg : ∀ i ∈ s, 0 ≤ w i * g i ^ 2 :=
    fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hsq : (∑ i ∈ s, w i * f i * g i) ^ 2 ≤
      (∑ i ∈ s, w i * f i ^ 2) * ∑ i ∈ s, w i * g i ^ 2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hf hg
    intro i _
    exact le_of_eq (by ring)
  exact (Real.le_sqrt_of_sq_le hsq).trans_eq
    (Real.sqrt_mul (sum_nonneg hf) _)

/-- Multiplicativity factors a rectangular character sum exactly. -/
theorem character_rectangular_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s t : Finset ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ s, ∑ n ∈ t, a m * b n * χ (m * n)) =
      (∑ m ∈ s, a m * χ m) * ∑ n ∈ t, b n * χ n := by
  simp only [map_mul, sum_mul_sum]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  ring

/-- A rectangular primitive-character first moment. There is no condition
on the relative order of the endpoints, so empty intervals are included. -/
theorem primitive_character_rectangular_bilinear_le (Q M N U V : ℕ)
    (a b : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ m ∈ Ico M N, ∑ n ∈ Ico U V, a m * b n * χ (m * n)‖)) ≤
      Real.sqrt (characterLargeSieveConstant Q M N * ∑ m ∈ Ico M N, ‖a m‖ ^ 2) *
        Real.sqrt (characterLargeSieveConstant Q U V * ∑ n ∈ Ico U V, ‖b n‖ ^ 2) := by
  simp_rw [character_rectangular_sum_eq, norm_mul]
  let s : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
    (Icc 1 Q).sigma fun q =>
      (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)
  let w : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun p =>
    (p.1 : ℝ) / Nat.totient p.1
  let f : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun p =>
    ‖∑ m ∈ Ico M N, a m * p.2 m‖
  let g : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun p =>
    ‖∑ n ∈ Ico U V, b n * p.2 n‖
  have hcs := weighted_sum_mul_le_sqrt_mul_sqrt s w f g
    (fun p _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ Real.sqrt (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ m ∈ Ico M N, a m * χ m‖ ^ 2)) *
        Real.sqrt (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
          (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ico U V, b n * χ n‖ ^ 2)) := by
      simpa only [s, w, f, g, sum_sigma, mul_sum, mul_assoc] using hcs
    _ ≤ _ := mul_le_mul
      (Real.sqrt_le_sqrt (primitive_character_large_sieve_log_direct Q M N a))
      (Real.sqrt_le_sqrt (primitive_character_large_sieve_log_direct Q U V b))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The same rectangular bound in the inverse-character convention. -/
theorem primitive_character_rectangular_bilinear_inv_le (Q M N U V : ℕ)
    (a b : ℕ → ℂ) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ m ∈ Ico M N, ∑ n ∈ Ico U V, a m * b n * χ⁻¹ (m * n)‖)) ≤
      Real.sqrt (characterLargeSieveConstant Q M N * ∑ m ∈ Ico M N, ‖a m‖ ^ 2) *
        Real.sqrt (characterLargeSieveConstant Q U V * ∑ n ∈ Ico U V, ‖b n‖ ^ 2) := by
  have heq (q : ℕ) := sum_primitive_character_inv_eq q
    (fun χ => ‖∑ m ∈ Ico M N, ∑ n ∈ Ico U V, a m * b n * χ (m * n)‖)
  simp_rw [heq]
  exact primitive_character_rectangular_bilinear_le Q M N U V a b

end TwinPrime.Analytic
