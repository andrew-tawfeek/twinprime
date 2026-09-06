import TwinPrime.ConditionalBilinear
import TwinPrime.Analytic.BombieriVinogradovFromSW

/-!
# The twin-prime endpoint from Siegel--Walfisz and the signed bilinear bound

The classical distribution input is now reduced to independent centered
pointwise Siegel--Walfisz. That statement and the signed fixed-shift bound
remain explicit unproved hypotheses.
-/

noncomputable section

open TwinPrime.Analytic

namespace TwinPrime

theorem twinPrimeConjecture_of_siegel_walfisz_and_bilinear
    (hSW : PointwiseSiegelWalfisz)
    (hB : ∀ Y : ℕ, ∃ X ≥ Y,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture :=
  twinPrimeConjecture_of_bv_and_bilinear hSW.bombieriVinogradov hB

end TwinPrime
