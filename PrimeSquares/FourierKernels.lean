import PrimeSquares.SquareFourier

/-!
# Inverse Fourier kernels and finite convolution

A continuous symbol's inverse transform is a genuine integer l2 sequence.
Its associated multiplier agrees with convolution for every finite complex
input, and supplies KernelL2Bound with the proved symbol norm bound.
No compact-support or positivity assertion is made for these new kernels.
-/

open Finset MeasureTheory
open scoped lp

namespace PrimeSquares

noncomputable def fourierKernelSequence (m : C(PrimeCircle, ℂ)) : ℓ²(ℤ, ℂ) :=
  integerFourier.symm (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ m)

noncomputable def fourierKernel (m : C(PrimeCircle, ℂ)) (x : ℤ) : ℂ :=
  fourierKernelSequence m x

theorem integerFourier_kernel (m : C(PrimeCircle, ℂ)) :
    integerFourier (fourierKernelSequence m) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ m := integerFourier.apply_symm_apply _

theorem fourierKernel_coefficient (m : C(PrimeCircle, ℂ)) (x : ℤ) :
    fourierKernel m x = fourierCoeff m (-x) := by
  have h := integerFourier_coefficient (fourierKernelSequence m) x
  rw [integerFourier_kernel, fourierCoeff_toLp] at h
  exact h.symm

theorem integerMultiplier_single_translate (m : C(PrimeCircle, ℂ)) (i : ℤ) (z : ℂ) :
    integerMultiplier m (lp.single 2 i z) =
      z • integerTranslate (P := 2) (by norm_num) i (fourierKernelSequence m) := by
  apply integerFourier.injective
  rw [integerFourier_multiplier, integerFourier_single, map_smul, map_smul,
    integerFourier_translate, integerFourier_kernel]
  change z • circleMultiply m
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (negativeFourierCharacter i)) =
    z • circleMultiply (negativeFourierCharacter i)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ m)
  rw [circleMultiply_toLp, circleMultiply_toLp, mul_comm m]

theorem integerMultiplier_single_convolution (m : C(PrimeCircle, ℂ))
    (i : ℤ) (z : ℂ) (x : ℤ) :
    integerMultiplier m (lp.single 2 i z) x = fourierKernel m (x-i) * z := by
  rw [integerMultiplier_single_translate]
  change z * integerTranslate (P := 2) (by norm_num) i (fourierKernelSequence m) x = _
  rw [integerTranslate_apply]
  exact mul_comm _ _

theorem integerMultiplier_finite_convolution (m : C(PrimeCircle, ℂ))
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    integerMultiplier m (finiteInputLp F f 2) x = finiteConvolution (fourierKernel m) F f x := by
  simp only [finiteInputLp, map_sum, lp.coeFn_sum, Finset.sum_apply, finiteConvolution]
  exact sum_congr rfl (fun i _ => integerMultiplier_single_convolution m i (f i) x)

theorem integerMultiplier_indicator_convolution (m : C(PrimeCircle, ℂ))
    (F : Finset ℤ) (x : ℤ) :
    integerMultiplier m (finiteIndicatorLp F 2) x = indicatorConvolution (fourierKernel m) F x := by
  rw [← finiteInputLp_one F 2, integerMultiplier_finite_convolution, finiteConvolution_indicator]

theorem fourierKernel_l2_bound (m : C(PrimeCircle, ℂ)) :
    KernelL2Bound (fourierKernel m) ‖m‖ := by
  exact ⟨integerMultiplier m,
    fun F x => (integerMultiplier_indicator_convolution m F x).symm,
    integerMultiplier_opNorm_le m⟩

theorem fourierKernel_l2_bound_of_bound (m : C(PrimeCircle, ℂ))
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ θ, ‖m θ‖ ≤ B) :
    KernelL2Bound (fourierKernel m) B := by
  exact ⟨integerMultiplier m,
    fun F x => (integerMultiplier_indicator_convolution m F x).symm,
    integerMultiplier_opNorm_le_of_bound m hB hm⟩

theorem finiteSquareSymbol_kernel (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (x : ℤ) :
    fourierKernel (finiteSquareSymbol S c w) x = finiteSquareKernel S c w x := by
  have hf := integerMultiplier_single_convolution (finiteSquareSymbol S c w) 0 1 x
  rw [← finiteSquareOperator_l2_multiplier, sub_zero, mul_one] at hf
  have he := finiteSquareKernel_finiteInput (P := 2) (by norm_num) S c w {0}
    (fun _ => (1 : ℂ)) x
  simp only [finiteInputLp, sum_singleton, finiteConvolution, sub_zero, mul_one] at he
  exact hf.symm.trans he.symm

end PrimeSquares
