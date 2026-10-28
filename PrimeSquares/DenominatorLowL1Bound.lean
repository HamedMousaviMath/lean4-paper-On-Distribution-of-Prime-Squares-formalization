import PrimeSquares.DenominatorLowKernelDecay
import PrimeSquares.KernelSensitiveFourierL1

open scoped lp
namespace PrimeSquares

theorem denominatorCircleLow_L1_norm {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) :
    ‖fourierL1Operator (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S)‖ ≤ physicalLowAmplitude N Q :=
  fourierL1Operator_opNorm_kernel_bound _ (denominatorCircleLow_kernel_uniform hN hQ hb q₀ χ₀ hχ hβ S hS hw)

theorem denominatorCircleLow_L1_bound {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (f : ℓ¹(ℤ, ℂ)) :
    ‖fourierL1Operator (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S) f‖ ≤ physicalLowAmplitude N Q*‖f‖ :=
  fourierL1Operator_kernel_bound _ (denominatorCircleLow_kernel_uniform hN hQ hb q₀ χ₀ hχ hβ S hS hw) f

end PrimeSquares
