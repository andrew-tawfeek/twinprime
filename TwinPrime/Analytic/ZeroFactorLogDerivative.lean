import TwinPrime.Analytic.HolomorphicZeroRemoval
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Logarithmic derivatives after removing the actual zeros

Finite divisor support turns the factorized rational function into a finite
product. Its logarithmic derivative is the sum of the actual multiplicities
divided by the displacement from each zero. The identity then applies to
the exact holomorphic zero-removal factorization.
-/

noncomputable section

open Finset Function MeromorphicOn Filter
open scoped Topology

namespace TwinPrime.Analytic

theorem logDeriv_sub_const_zpow (u z : ℂ) (m : ℤ) :
    logDeriv (fun w : ℂ => (w - u) ^ m) z = (m : ℂ) / (z - u) := by
  have hd : HasDerivAt (fun w : ℂ => w - u) 1 z := (hasDerivAt_id z).sub_const u
  rw [logDeriv_fun_zpow hd.differentiableAt m, logDeriv_apply, hd.deriv]
  ring

/-- A finite integer exponent function gives the exact logarithmic derivative
of its factorized rational function at every nonzero value. -/
theorem logDeriv_factorizedRational (d : ℂ → ℤ) (hd : d.HasFiniteSupport)
    (z : ℂ) (hP : (∏ᶠ u, (· - u) ^ d u) z ≠ 0) :
    logDeriv (∏ᶠ u, (· - u) ^ d u) z = ∑ᶠ u, (d u : ℂ) / (z - u) := by
  classical
  let S : Finset ℂ := hd.toFinset
  have hsupport : (fun u : ℂ => (fun w : ℂ => w - u) ^ d u).mulSupport ⊆ S := by
    rw [Function.FactorizedRational.mulSupport]
    intro u hu
    simpa [S] using hu
  have hpoly : (∏ᶠ u, (· - u) ^ d u) = fun w => ∏ u ∈ S, (w - u) ^ d u := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupport]
    ext w
    simp
  have hfac : ∀ u ∈ S, (z - u) ^ d u ≠ 0 := by
    rw [hpoly] at hP
    exact prod_ne_zero_iff.mp hP
  have hdiff : ∀ u ∈ S, DifferentiableAt ℂ (fun w : ℂ => (w - u) ^ d u) z := by
    intro u hu
    have hdu : d u ≠ 0 := by simpa [S] using hu
    have hzu : z - u ≠ 0 := by
      intro hzero
      exact hfac u hu (by rw [hzero, zero_zpow _ hdu])
    exact (differentiableAt_id.sub_const u).zpow (Or.inl hzu)
  rw [hpoly, logDeriv_prod (f := fun u w : ℂ => (w - u) ^ d u) hfac hdiff]
  have hsumSupport : (fun u : ℂ => (d u : ℂ) / (z - u)).support ⊆ S := by
    intro u hu
    apply hd.mem_toFinset.mpr
    intro hdu
    exact hu (by simp [hdu])
  rw [finsum_eq_sum_of_support_subset _ hsumSupport]
  exact sum_congr rfl (fun u _ => logDeriv_sub_const_zpow u z (d u))

theorem logDeriv_zeroFactorPolynomial (f : ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (z : ℂ) (hP : zeroFactorPolynomial f K z ≠ 0) :
    logDeriv (zeroFactorPolynomial f K) z =
      ∑ᶠ u, (divisor f K u : ℂ) / (z - u) :=
  logDeriv_factorizedRational (divisor f K) ((divisor f K).finiteSupport hK) z hP

/-- The finite zero-factor function is analytic at any point where its
totalized value is nonzero, even without assuming nonnegative exponents. -/
theorem analyticAt_zeroFactorPolynomial_of_ne_zero (f : ℂ → ℂ) (K : Set ℂ)
    (hK : IsCompact K) (z : ℂ) (hP : zeroFactorPolynomial f K z ≠ 0) :
    AnalyticAt ℂ (zeroFactorPolynomial f K) z := by
  have hd : (divisor f K).support.Finite := (divisor f K).finiteSupport hK
  have hdz : divisor f K z = 0 := by
    by_contra hdz
    have hfactor := congrFun (Function.FactorizedRational.extractFactor z hd) z
    apply hP
    simpa only [zeroFactorPolynomial, Pi.mul_apply, Pi.pow_apply, sub_self,
      zero_zpow _ hdz, zero_mul] using hfactor
  exact Function.FactorizedRational.analyticAt (by rw [hdz])

/-- Apply the exact zero-factor expansion to a given quotient. This preserves
the same quotient chosen by a separate boundary-growth argument. -/
theorem logDeriv_eq_zeroFactor_sum_add {f g : ℂ → ℂ} {U K : Set ℂ}
    (hU : IsOpen U) (_hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hK : IsCompact K) (hEq : ∀ w ∈ U, f w = zeroFactorPolynomial f K w * g w)
    (z : ℂ) (hz : z ∈ U) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ᶠ u, (divisor f K u : ℂ) / (z - u)) + logDeriv g z := by
  have hprod : zeroFactorPolynomial f K z * g z ≠ 0 := by rw [← hEq z hz]; exact hfz
  obtain ⟨hP, hgz⟩ := mul_ne_zero_iff.mp hprod
  have hlocal : f =ᶠ[𝓝 z] (fun w => zeroFactorPolynomial f K w * g w) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) (fun w hw => hEq w hw)
  calc
    logDeriv f z = logDeriv (fun w => zeroFactorPolynomial f K w * g w) z := by
      rw [logDeriv_apply, logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
    _ = logDeriv (zeroFactorPolynomial f K) z + logDeriv g z :=
      logDeriv_mul z hP hgz (analyticAt_zeroFactorPolynomial_of_ne_zero f K hK z hP).differentiableAt
        (hg.differentiableAt (hU.mem_nhds hz))
    _ = _ := by rw [logDeriv_zeroFactorPolynomial f K hK z hP]

/-- Existence of actual zero removal together with its logarithmic derivative
expansion at all nonzeros of the original function. -/
theorem exists_holomorphic_zero_removal_logDeriv {f : ℂ → ℂ} {U K : Set ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hc : c ∈ U) (hfc : f c ≠ 0) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ K, g z ≠ 0) ∧
      (∀ z ∈ U, f z = zeroFactorPolynomial f K z * g z) ∧
      ∀ z ∈ U, f z ≠ 0 →
        logDeriv f z = (∑ᶠ u, (divisor f K u : ℂ) / (z - u)) + logDeriv g z := by
  obtain ⟨g, hg, hgn, hEq⟩ := exists_holomorphic_zero_removal hf hconn hc hfc hK hKU
  refine ⟨g, hg, hgn, hEq, ?_⟩
  intro z hz hfz
  exact logDeriv_eq_zeroFactor_sum_add hU hf.differentiableOn hg.differentiableOn hK hEq z hz hfz

end TwinPrime.Analytic
