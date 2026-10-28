import PrimeSquares.CircleFiniteDecomposition
import PrimeSquares.KernelSensitiveFourierL1

namespace PrimeSquares

theorem circleLowOperator_kernel_bound (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B₀ : ℝ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (β : ℝ) {B : ℝ} (hK : ∀ x, ‖circleLowKernel Γ N hN q₀ Q B₀ χ κ β x‖ ≤ B) :
    ‖circleLowOperator Γ N hN q₀ Q B₀ χ κ β‖ ≤ B :=
  fourierL1Operator_opNorm_kernel_bound _ hK

theorem circleHighOperator_symbol_bound (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B₀ : ℝ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (β : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ θ, ‖circleHighModel Γ N hN q₀ Q B₀ χ κ β θ‖ ≤ B) :
    ‖circleHighOperator Γ N hN q₀ Q B₀ χ κ β‖ ≤ B :=
  integerMultiplier_opNorm_le_of_bound _ hB hm

end PrimeSquares
