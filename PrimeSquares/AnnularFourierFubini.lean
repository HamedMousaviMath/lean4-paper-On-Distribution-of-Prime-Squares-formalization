import PrimeSquares.AnnularFourierIntegrand

open MeasureTheory
namespace PrimeSquares

theorem annularFourierIntegrand_swap {N : ℕ} (hN : 1 ≤ N) (β a x : ℝ) :
    (∫ ξ in (-(1/2) : ℝ)..(1/2),∫ t in (N : ℝ)/2..N,annularFourierIntegrand β a x ξ t)=
      ∫ t in (N : ℝ)/2..N,∫ ξ in (-(1/2) : ℝ)..(1/2),annularFourierIntegrand β a x ξ t := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2),
    intervalIntegral.integral_of_le (by linarith : (N : ℝ)/2 ≤ N)] using
      integral_integral_swap (annularFourierIntegrand_integrable hN β a x)

end PrimeSquares
