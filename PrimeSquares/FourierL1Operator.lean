import PrimeSquares.KernelL1FiniteAgreement

open scoped lp
namespace PrimeSquares

noncomputable def fourierL1Operator (m : C(PrimeCircle, ℂ)) :
    ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤ :=
  kernelL1Operator (fourierKernel m)
    (fourierKernel_uniform_bound m (fun θ => m.norm_coe_le_norm θ))

theorem fourierL1Operator_norm (m : C(PrimeCircle, ℂ)) : ‖fourierL1Operator m‖ ≤ ‖m‖ :=
  kernelL1Operator_norm _ _

theorem fourierL1Operator_l2_agreement (m : C(PrimeCircle, ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    fourierL1Operator m (finiteInputLp F f 1) x =
      integerMultiplier m (finiteInputLp F f 2) x := by
  exact (kernelL1Operator_finite _ _ F f x).trans
    (integerMultiplier_finite_convolution m F f x).symm

end PrimeSquares
