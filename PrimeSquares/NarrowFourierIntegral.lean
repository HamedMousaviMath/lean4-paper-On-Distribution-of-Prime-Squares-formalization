import PrimeSquares.SourceArcCutoff
import PrimeSquares.RealInverseFourierIntegral

open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem narrow_inverse_fourier_interval (f : ℝ → ℂ)
    (hf : ∀ ξ : ℝ,1/2 ≤ |ξ| → f ξ=0) (x : ℝ) :
    𝓕⁻ f x=∫ ξ in (-(1/2) : ℝ)..(1/2),realFourierPhase (ξ*x)*f ξ := by
  rw [real_inverse_fourier_integral,intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro ξ hξ
  have ha : 1/2 ≤ |ξ| := by
    rw [Set.mem_Ioc,not_and_or] at hξ
    rcases hξ with h | h
    · have h' : ξ ≤ -(1/2) := le_of_not_gt h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h' : 1/2 < ξ := lt_of_not_ge h
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [hf ξ ha,mul_zero]

theorem scaled_source_cutoff_narrow {a : ℝ} (ha : 2 ≤ a) {ξ : ℝ} (hξ : 1/2 ≤ |ξ|) :
    sourceArcCutoff (a*ξ)=0 := by
  apply sourceArcCutoff_zero
  rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ a)]
  nlinarith

end PrimeSquares
