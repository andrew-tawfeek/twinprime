import TwinPrime.ConditionalBilinear
import TwinPrime.Analytic.ClassicalDistribution

/-!
# The twin-prime endpoint with only the signed bilinear estimate assumed

The classical distribution input is supplied by the proved Siegel--Walfisz,
Bombieri--Vinogradov, and Mertens chain. The cofinal fixed-shift bound is
still an explicit hypothesis: this is not an unconditional twin-prime proof.
-/

noncomputable section

open TwinPrime.Analytic

namespace TwinPrime

theorem twinPrimeConjecture_of_signed_bilinear
    (hB : ∀ Y : ℕ, ∃ X ≥ Y,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture :=
  twinPrimeConjecture_of_bv_and_bilinear maximal_bombieri_vinogradov hB

end TwinPrime
