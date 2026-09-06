import TwinPrime.Analytic.SiegelWalfiszTheorem
import TwinPrime.Analytic.BombieriVinogradovFromSW
import TwinPrime.Analytic.PrimeToMertens

/-!
# Unconditional classical distribution inputs

The independently proved pointwise Siegel--Walfisz theorem supplies the
existing maximalization, Bombieri--Vinogradov assembly, and quantitative
Mertens reduction. These results make no signed fixed-shift assumption.
-/

namespace TwinPrime.Analytic

theorem maximal_siegel_walfisz : MaximalSiegelWalfisz :=
  pointwise_siegel_walfisz.maximal

theorem maximal_bombieri_vinogradov : MaximalBombieriVinogradov :=
  pointwise_siegel_walfisz.bombieriVinogradov

theorem mertens_log_six : MertensLogSix :=
  maximal_bombieri_vinogradov.mertensLogSix

end TwinPrime.Analytic
