import PrimeSquares.SourceLowFullRangeBounds
import PrimeSquares.PhysicalLowPairing

open Finset
namespace PrimeSquares

theorem uniformKernel_indicator_bound (K : ℤ → ℂ) {B : ℝ} (hK : ∀ x,‖K x‖ ≤ B)
    (F : Finset ℤ) (x : ℤ) : ‖indicatorConvolution K F x‖ ≤ B*(F.card : ℝ) := by
  calc
    _ ≤ ∑ y ∈ F,‖K (x-y)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ F,B := sum_le_sum (fun y _ => hK (x-y))
    _ = _ := by simp [mul_comm]

theorem uniformKernel_pairing_bound (K : ℤ → ℂ) {B : ℝ} (hK : ∀ x,‖K x‖ ≤ B)
    (F G : Finset ℤ) : ‖restrictedKernelPairing K F G‖ ≤ B*(F.card : ℝ)*(G.card : ℝ) := by
  calc
    _ ≤ ∑ x ∈ G,‖indicatorConvolution K F x‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G,B*(F.card : ℝ) := sum_le_sum (fun x _ => uniformKernel_indicator_bound K hK F x)
    _ = _ := by simp [mul_comm]

theorem sourceFullLow_pairing {N : ℕ} (hN : 2 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (active : Bool) {β : ℝ} (hβ : β ≤ 1)
    {Q R : ℝ} (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2) (F G : Finset ℤ) :
    ‖restrictedKernelPairing (fourierKernel (circleLowModel (sourceRationalCenters R) N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β)) F G‖ ≤
      (2*realLowAmplitude N Q)*(F.card : ℝ)*(G.card : ℝ) := by
  apply uniformKernel_pairing_bound
  intro x
  rw [sourceFullLow_squared (by omega) q₀ χ₀ active β (by linarith) hQR hb]
  exact realCombinedLowModel_uniform hN hQ _ q₀ χ₀ hχ hβ ⌊R⌋₊ active x

end PrimeSquares
