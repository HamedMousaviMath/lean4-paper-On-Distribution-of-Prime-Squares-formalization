import PrimeSquares.AnnularFourierFubini
import PrimeSquares.AnnularCutoffSymbol

namespace PrimeSquares

theorem annular_phase_factorization (ξ x t : ℝ) :
    realFourierPhase (ξ*x)*quadraticOscillation ξ t=realFourierPhase (ξ*(x-t^2)) := by
  rw [realFourierPhase_quadratic,←realFourierPhase_add]
  congr 1
  ring

theorem annular_cutoff_phase_integral {N : ℕ} (hN : 1 ≤ N) (β a x ξ : ℝ) :
    realFourierPhase (ξ*x)*annularCutoffSymbol N hN β a ξ=
      Complex.ofReal (N : ℝ)⁻¹*∫ t in (N : ℝ)/2..N,annularFourierIntegrand β a x ξ t := by
  have he (t : ℝ) : annularFourierIntegrand β a x ξ t=
      realFourierPhase (ξ*x)*(Complex.ofReal (t^(β-1))*quadraticOscillation ξ t)*
        Complex.ofReal (sourceArcCutoff (a*ξ)) := by
    unfold annularFourierIntegrand
    rw [←annular_phase_factorization]
    ring
  have hi : (∫ t in (N : ℝ)/2..N,annularFourierIntegrand β a x ξ t)=
      realFourierPhase (ξ*x)*(∫ t in (N : ℝ)/2..N,Complex.ofReal (t^(β-1))*quadraticOscillation ξ t)*
        Complex.ofReal (sourceArcCutoff (a*ξ)) := by
    simp_rw [he]
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
  change realFourierPhase (ξ*x)*(annularOscillatoryModel N β ξ*Complex.ofReal (sourceArcCutoff (a*ξ)))=_
  rw [hi,annularOscillatoryModel_interval]
  ring

end PrimeSquares
