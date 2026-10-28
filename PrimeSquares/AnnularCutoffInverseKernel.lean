import PrimeSquares.AnnularPhaseFactorization
import PrimeSquares.ScaledCutoffInverseIdentity
import PrimeSquares.SmoothedAnnularKernel

open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem annular_cutoff_inverse_transform {N : ℕ} (hN : 1 ≤ N) (β : ℝ) {a : ℝ}
    (ha : 2 ≤ a) (x : ℝ) :
    𝓕⁻ (annularCutoffSymbol N hN β a : ℝ → ℂ) x=smoothedAnnularKernel N β a x := by
  have hap : 0 < a := by linarith
  rw [narrow_inverse_fourier_interval _ (fun ξ hξ => annularCutoffSymbol_narrow N hN β ha hξ)]
  simp_rw [annular_cutoff_phase_integral hN β a x]
  rw [intervalIntegral.integral_const_mul,annularFourierIntegrand_swap hN]
  have hi (t : ℝ) : (∫ ξ in (-(1/2) : ℝ)..(1/2),annularFourierIntegrand β a x ξ t)=
      Complex.ofReal (t^(β-1))*scaledCutoffKernel a (x-t^2) := by
    have he : (∫ ξ in (-(1/2) : ℝ)..(1/2),realFourierPhase (ξ*(x-t^2))*
        Complex.ofReal (sourceArcCutoff (a*ξ)))=scaledCutoffKernel a (x-t^2) := by
      rw [←scaledCutoffKernel_inverse_transform hap,
        narrow_inverse_fourier_interval _ (fun ξ hξ => congrArg Complex.ofReal (scaled_source_cutoff_narrow ha hξ))]
    simp only [annularFourierIntegrand,mul_assoc,intervalIntegral.integral_const_mul]
    rw [he]
  simp_rw [hi]
  rfl

end PrimeSquares
