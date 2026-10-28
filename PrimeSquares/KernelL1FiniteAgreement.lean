import PrimeSquares.KernelL1Operator

open Finset
open scoped lp
namespace PrimeSquares

theorem kernelL1Operator_finite (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    kernelL1Operator K hK (finiteInputLp F f 1) x = finiteConvolution K F f x := by
  rw [kernelL1Operator_apply]
  rw [tsum_eq_sum (s := F) (fun y hy => by simp [finiteInputLp_apply,hy])]
  apply sum_congr rfl
  intro y hy
  simp only [finiteInputLp_apply,ite_eq_left hy]

theorem kernelL1Operator_indicator (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (F : Finset ℤ) (x : ℤ) :
    kernelL1Operator K hK (finiteIndicatorLp F 1) x = indicatorConvolution K F x := by
  rw [← finiteInputLp_one, kernelL1Operator_finite, finiteConvolution_indicator]

end PrimeSquares
