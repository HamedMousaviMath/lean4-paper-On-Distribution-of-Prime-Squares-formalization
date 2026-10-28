import PrimeSquares.CircleModelKernelBounds
import PrimeSquares.CircleModelOperators
import PrimeSquares.KernelSensitiveFourierL1

open Finset
namespace PrimeSquares

theorem circleMajorArcOperator_bound {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1) :
    ‖circleMajorArcOperator Γ N (by omega) χ κ β‖ ≤
      ∑ r ∈ Γ, 3*(gaussModelConstant*(r.den : ℝ)^(-(5/12 : ℝ))) := by
  apply integerMultiplier_opNorm_le_of_bound
  · exact sum_nonneg fun _ _ => by have hc := gaussModelConstant_pos;positivity
  · exact circleMajorArcModel_norm hN Γ χ κ hβ0 hβ1 hκ

theorem circleMajorArcL1Operator_bound {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1) :
    ‖fourierL1Operator (circleMajorArcModel Γ N (by omega) χ κ β)‖ ≤
      ∑ r ∈ Γ, 3*(gaussModelConstant*(r.den : ℝ)^(-(5/12 : ℝ))) :=
  fourierL1Operator_opNorm_kernel_bound _ (circleModelKernel_bound hN Γ χ κ hβ0 hβ1 hκ)

end PrimeSquares
