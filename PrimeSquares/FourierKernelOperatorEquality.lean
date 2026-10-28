import PrimeSquares.AllInputFourierConvolution

open scoped lp
namespace PrimeSquares

theorem integerMultiplier_eq_of_kernel {m n : C(PrimeCircle, ℂ)}
    (h : ∀ x : ℤ,fourierKernel m x=fourierKernel n x) : integerMultiplier m=integerMultiplier n := by
  ext f x
  rw [integerMultiplier_all_convolution,integerMultiplier_all_convolution]
  exact tsum_congr (fun y => congrArg (fun z : ℂ => z*f y) (h (x-y)))

theorem fourierL1Operator_eq_of_kernel {m n : C(PrimeCircle, ℂ)}
    (h : ∀ x : ℤ,fourierKernel m x=fourierKernel n x) : fourierL1Operator m=fourierL1Operator n := by
  ext f x
  rw [fourierL1Operator_all_l2_agreement,fourierL1Operator_all_l2_agreement,integerMultiplier_eq_of_kernel h]

end PrimeSquares
