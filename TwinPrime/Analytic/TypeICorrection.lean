import TwinPrime.Analytic.LogarithmicCorrection
import TwinPrime.Analytic.TypeICorrelation
import TwinPrime.Analytic.TotientMainAsymptotics
import TwinPrime.Analytic.CutoffLogarithms

/-!
# The Type I correction from separate classical inputs

Both parts of `K = H - I` have sublinear growth under the stated distribution
and logarithmic Möbius/totient cancellation hypotheses. Those two classical
inputs are theorem arguments and are not proved in this module.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

theorem tendsto_typeICorrection_div_of_inputs (hBV : MaximalBombieriVinogradov)
    (hM : Tendsto (fun t : ℕ =>
      oddMoebiusTotientSum t * (Real.log ((t : ℝ) + 1)) ^ 2) atTop (nhds 0)) :
    Tendsto (fun X : ℕ => typeICorrection (primaryCutoff X) (primaryCutoff X) X / X)
      atTop (nhds 0) := by
  have hH := tendsto_logarithmicCorrection_div_of_inputs hBV
    (tendsto_primary_mul_log_of_mul_log_sq_tendsto_zero oddMoebiusTotientSum hM)
  have hI := tendsto_typeITerm_div_of_inputs hBV
    (tendsto_totientTypeIMain_same_cutoff hM primaryCutoff tendsto_primaryCutoff)
  simpa only [typeICorrection, sub_div, sub_zero] using hH.sub hI

end TwinPrime.Analytic
