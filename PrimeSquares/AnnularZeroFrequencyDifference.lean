import PrimeSquares.AnnularDifferenceIntegrand
open MeasureTheory
namespace PrimeSquares
theorem annularOscillatoryModel_sub_zero {N : ℕ} (hN : 1 ≤ N) (β θ : ℝ) :
    annularOscillatoryModel N β θ-annularOscillatoryModel N β 0=
      Complex.ofReal ((N : ℝ)⁻¹)*∫ t in (N : ℝ)/2..N,
        Complex.ofReal (t^(β-1))*(quadraticOscillation θ t-1) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hab : (N : ℝ)/2 ≤ N := by linarith
  have hi (u : ℝ) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (annularOscillatoryIntegrand_integrable hN β u)
  rw [annularOscillatoryModel_interval,annularOscillatoryModel_interval,←mul_sub,
    ←intervalIntegral.integral_sub (hi θ) (hi 0)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [quadraticOscillation,mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
  ring
end PrimeSquares
