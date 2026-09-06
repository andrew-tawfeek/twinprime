import TwinPrime.Analytic.LFunctionQuadraticZeroFree
import TwinPrime.Analytic.LFunctionNearOneZeros

/-!
# A primitive L-function zero-free region with a possible real exception

The budget combines both character-square cases and the near-one rectangle.
The remaining zero, if present, is quadratic, real, simple, and unique for
the given primitive character. No lower bound for its distance from one
is asserted here.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

def primitiveZeroFreeBudget (q : ℕ) (t : ℝ) : ℝ :=
  nonquadraticZeroFreeBudget q t + quadraticZeroFreeBudget q t + 4 * nearOneZeroBudget q

def primitiveZeroFreeWidth (q : ℕ) (t : ℝ) : ℝ := 1 / (40 * primitiveZeroFreeBudget q t)

theorem primitiveZeroFreeBudget_bounds (q : ℕ) (t : ℝ) :
    120 ≤ primitiveZeroFreeBudget q t ∧
      nonquadraticZeroFreeBudget q t ≤ primitiveZeroFreeBudget q t ∧
      quadraticZeroFreeBudget q t ≤ primitiveZeroFreeBudget q t ∧
      4 * nearOneZeroBudget q ≤ primitiveZeroFreeBudget q t := by
  have hn := nonquadraticZeroFreeBudget_ge q t
  have hq := quadraticZeroFreeBudget_ge q t
  have hK := primitiveLFunctionLogBudget_nonneg q 0
  have hnear : 40 ≤ nearOneZeroBudget q := by unfold nearOneZeroBudget; linarith
  unfold primitiveZeroFreeBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem primitiveZeroFreeWidth_pos (q : ℕ) (t : ℝ) :
    0 < primitiveZeroFreeWidth q t := by
  have h := (primitiveZeroFreeBudget_bounds q t).1
  unfold primitiveZeroFreeWidth
  positivity

theorem primitiveZeroFreeWidth_le_nonquadratic (q : ℕ) (t : ℝ) :
    primitiveZeroFreeWidth q t ≤ 1 / (20 * nonquadraticZeroFreeBudget q t) := by
  have hn := nonquadraticZeroFreeBudget_ge q t
  have hR := (primitiveZeroFreeBudget_bounds q t).2.1
  unfold primitiveZeroFreeWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 20 * nonquadraticZeroFreeBudget q t)
  linarith

theorem primitiveZeroFreeWidth_le_nearOne (q : ℕ) (t : ℝ) :
    primitiveZeroFreeWidth q t ≤ nearOneZeroWidth q := by
  have hK := primitiveLFunctionLogBudget_nonneg q 0
  have hnear : 40 ≤ nearOneZeroBudget q := by unfold nearOneZeroBudget; linarith
  have hR := (primitiveZeroFreeBudget_bounds q t).2.2.2
  unfold primitiveZeroFreeWidth nearOneZeroWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 16 * nearOneZeroBudget q)
  linarith

theorem primitiveZeroFreeHeight_le_nearOne (q : ℕ) (t : ℝ) :
    1 / (4 * primitiveZeroFreeBudget q t) ≤ nearOneZeroWidth q := by
  have hK := primitiveLFunctionLogBudget_nonneg q 0
  have hnear : 40 ≤ nearOneZeroBudget q := by unfold nearOneZeroBudget; linarith
  have hR := (primitiveZeroFreeBudget_bounds q t).2.2.2
  unfold nearOneZeroWidth
  apply one_div_le_one_div_of_le (by linarith : 0 < 16 * nearOneZeroBudget q)
  linarith

/-- Every zero in the stated uniform region belongs to the small quadratic
rectangle. This conclusion does not assume that the character is real. -/
theorem LFunction_zero_in_region_near_one {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β t : ℝ) (hβ : 1 - primitiveZeroFreeWidth q t ≤ β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    χ ^ 2 = 1 ∧ 1 - nearOneZeroWidth q ≤ β ∧ |t| ≤ nearOneZeroWidth q := by
  have hχ2 : χ ^ 2 = 1 := by
    by_contra hχ2
    have hwidth := primitiveZeroFreeWidth_le_nonquadratic q t
    exact LFunction_ne_zero_of_nonquadratic hq χ hχ hχ2 β t (by linarith) hzero
  have ht : |t| < 1 / (4 * primitiveZeroFreeBudget q t) := by
    by_contra ht
    exact LFunction_ne_zero_of_quadratic_large_height_of_budget hq χ hχ hχ2 β t
      (primitiveZeroFreeBudget q t) (primitiveZeroFreeBudget_bounds q t).2.2.1
      hβ (not_lt.mp ht) hzero
  refine ⟨hχ2, ?_, ht.le.trans (primitiveZeroFreeHeight_le_nearOne q t)⟩
  have hwidth := primitiveZeroFreeWidth_le_nearOne q t
  linarith

/-- A zero in the uniform region is a simple real zero of a quadratic
character. The order is the actual meromorphic order of the L-function. -/
theorem LFunction_zero_in_region_real_simple {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β t : ℝ) (hβ : 1 - primitiveZeroFreeWidth q t ≤ β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * t) = 0) :
    χ ^ 2 = 1 ∧ t = 0 ∧
      meromorphicOrderAt (DirichletCharacter.LFunction χ) (β : ℂ) = 1 := by
  obtain ⟨hχ2, hnear, htnear⟩ := LFunction_zero_in_region_near_one hq χ hχ β t hβ hzero
  let ρ : ℂ := (β : ℂ) + Complex.I * t
  have hρre : 1 - nearOneZeroWidth q ≤ ρ.re := by simpa [ρ] using hnear
  have hρim : |ρ.im| ≤ nearOneZeroWidth q := by simpa [ρ] using htnear
  have hreal := nearOne_zero_real_of_sq_eq_one hq χ hχ hχ2 ρ hρre hρim hzero
  have ht0 : t = 0 := by simpa [ρ] using hreal
  have horder := nearOne_zero_order_eq_one hq χ hχ ρ hρre hρim hzero
  exact ⟨hχ2, ht0, by simpa [ρ, ht0] using horder⟩

/-- The region contains at most one zero for the fixed primitive character,
even when the two points are described using different height budgets. -/
theorem LFunction_zero_in_region_unique {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (β₁ t₁ β₂ t₂ : ℝ)
    (hβ₁ : 1 - primitiveZeroFreeWidth q t₁ ≤ β₁)
    (hz₁ : DirichletCharacter.LFunction χ ((β₁ : ℂ) + Complex.I * t₁) = 0)
    (hβ₂ : 1 - primitiveZeroFreeWidth q t₂ ≤ β₂)
    (hz₂ : DirichletCharacter.LFunction χ ((β₂ : ℂ) + Complex.I * t₂) = 0) :
    β₁ = β₂ ∧ t₁ = t₂ := by
  obtain ⟨_, hn₁, ht₁⟩ := LFunction_zero_in_region_near_one hq χ hχ β₁ t₁ hβ₁ hz₁
  obtain ⟨_, hn₂, ht₂⟩ := LFunction_zero_in_region_near_one hq χ hχ β₂ t₂ hβ₂ hz₂
  have heq := nearOne_zero_unique hq χ hχ
    ((β₁ : ℂ) + Complex.I * t₁) ((β₂ : ℂ) + Complex.I * t₂)
    (by simpa using hn₁) (by simpa using ht₁) hz₁
    (by simpa using hn₂) (by simpa using ht₂) hz₂
  exact ⟨by simpa using congrArg Complex.re heq, by simpa using congrArg Complex.im heq⟩

end TwinPrime.Analytic
