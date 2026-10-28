import PrimeSquares.FourierL1Operator
import PrimeSquares.LpInclusion

open scoped lp
namespace PrimeSquares

theorem integerMultiplier_convolution_hasSum (m : C(PrimeCircle, ℂ)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    HasSum (fun y : ℤ => fourierKernel m (x-y)*f y) (integerMultiplier m f x) := by
  have h := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 x).hasSum
    ((integerMultiplier m).hasSum (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f))
  change HasSum (fun y : ℤ => integerMultiplier m (lp.single 2 y (f y)) x) (integerMultiplier m f x) at h
  simpa only [integerMultiplier_single_convolution] using h

theorem integerMultiplier_all_convolution (m : C(PrimeCircle, ℂ)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    integerMultiplier m f x=∑' y : ℤ,fourierKernel m (x-y)*f y :=
  (integerMultiplier_convolution_hasSum m f x).tsum_eq.symm

theorem fourierL1Operator_all_l2_agreement (m : C(PrimeCircle, ℂ)) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    fourierL1Operator m f x=
      integerMultiplier m (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x := by
  rw [integerMultiplier_all_convolution]
  rfl

end PrimeSquares
