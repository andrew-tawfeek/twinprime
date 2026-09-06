import TwinPrime.Analytic.SiegelZeroGapUnconditional

/-!
# Uniform zero-free rectangles from the actual Siegel gap

The width is the smaller of the logarithmic width at the largest height
and half the proved power gap. The positive constant is chosen before
the conductor, character, and height. Regularized zeta is treated separately
and retains its nonzero value at one.
-/

noncomputable section

namespace TwinPrime.Analytic

theorem primitiveLogZeroFreeWidth_antitone_abs (q : ℕ) {t H : ℝ}
    (ht : |t| ≤ |H|) :
    primitiveLogZeroFreeWidth q H ≤ primitiveLogZeroFreeWidth q t := by
  have hq := Real.log_natCast_nonneg q
  have htlog : 0 ≤ Real.log (|t| + 4) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_pos
  unfold primitiveLogZeroFreeWidth
  apply one_div_le_one_div_of_le (by positivity)
  have hl : Real.log (|t| + 4) ≤ Real.log (|H| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem zetaLogZeroFreeWidth_antitone_abs {t H : ℝ} (ht : |t| ≤ |H|) :
    zetaLogZeroFreeWidth H ≤ zetaLogZeroFreeWidth t := by
  have htlog : 0 ≤ Real.log (|t| + 4) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hC := zeroFreeLogConstant_pos
  unfold zetaLogZeroFreeWidth
  apply one_div_le_one_div_of_le (by positivity)
  have hl : Real.log (|t| + 4) ≤ Real.log (|H| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def primitiveZeroFreeRectangleWidth (ε d : ℝ) (q : ℕ) (H : ℝ) : ℝ :=
  min (1 / 16) (min (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε))) / 2

theorem primitiveZeroFreeRectangleWidth_pos (ε d : ℝ) (hd : 0 < d)
    (q : ℕ) [NeZero q] (H : ℝ) :
    0 < primitiveZeroFreeRectangleWidth ε d q H := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hw := primitiveLogZeroFreeWidth_pos q H
  unfold primitiveZeroFreeRectangleWidth
  positivity

theorem primitiveZeroFreeRectangleWidth_le_one_thirtysecond
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    primitiveZeroFreeRectangleWidth ε d q H ≤ 1 / 32 := by
  unfold primitiveZeroFreeRectangleWidth
  have := min_le_left (1 / 16 : ℝ)
    (min (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

theorem twice_primitiveZeroFreeRectangleWidth_le_log_width
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    2 * primitiveZeroFreeRectangleWidth ε d q H ≤ primitiveLogZeroFreeWidth q H := by
  unfold primitiveZeroFreeRectangleWidth
  have h := (min_le_right (1 / 16 : ℝ) _).trans
    (min_le_left (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

theorem twice_primitiveZeroFreeRectangleWidth_le_power_gap
    (ε d : ℝ) (q : ℕ) (H : ℝ) :
    2 * primitiveZeroFreeRectangleWidth ε d q H ≤ d * (q : ℝ) ^ (-ε) := by
  unfold primitiveZeroFreeRectangleWidth
  have h := (min_le_right (1 / 16 : ℝ) _).trans
    (min_le_right (primitiveLogZeroFreeWidth q H) (d * (q : ℝ) ^ (-ε)))
  linarith

/-- An actual uniform family of zero-free rectangles, without a supplied
value bound, zero-gap bound, or prime-distribution premise. -/
theorem exists_LFunction_zero_free_rectangle (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ (q : ℕ) [NeZero q], 1 < q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        ∀ (H : ℝ), 0 ≤ H → ∀ s : ℂ,
          1 - primitiveZeroFreeRectangleWidth ε d q H ≤ s.re →
          |s.im| ≤ H → DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨d, hd, hgap⟩ := LFunction_zero_in_log_region_power_gap ε hε
  refine ⟨d, hd, ?_⟩
  intro q _ hq χ hχ H hH s hs hsim hzero
  have hwpos := primitiveZeroFreeRectangleWidth_pos ε d hd q H
  have hwlog := twice_primitiveZeroFreeRectangleWidth_le_log_width ε d q H
  have hmono := primitiveLogZeroFreeWidth_antitone_abs q
    (t := s.im) (H := H) (by simpa only [abs_of_nonneg hH] using hsim)
  have hslog : 1 - primitiveLogZeroFreeWidth q s.im ≤ s.re := by linarith
  have heq : (s.re : ℂ) + Complex.I * s.im = s := by
    simpa only [mul_comm] using s.re_add_im
  have hz := hgap q hq χ hχ s.re s.im hslog (by rwa [heq])
  have hwpow := twice_primitiveZeroFreeRectangleWidth_le_power_gap ε d q H
  linarith [hz.2.2]

/-- Zeta's separate rectangle includes the pole after regularization. -/
theorem regularizedRiemannZeta_ne_zero_on_rectangle (H : ℝ) (hH : 0 ≤ H)
    (s : ℂ) (hs : 1 - zetaLogZeroFreeWidth H ≤ s.re) (hsim : |s.im| ≤ H) :
    regularizedRiemannZeta s ≠ 0 := by
  have hmono := zetaLogZeroFreeWidth_antitone_abs
    (t := s.im) (H := H) (by simpa only [abs_of_nonneg hH] using hsim)
  have h := regularizedRiemannZeta_ne_zero_of_log_region s.re s.im (by linarith)
  have heq : (s.re : ℂ) + Complex.I * s.im = s := by
    simpa only [mul_comm] using s.re_add_im
  rwa [heq] at h

end TwinPrime.Analytic
