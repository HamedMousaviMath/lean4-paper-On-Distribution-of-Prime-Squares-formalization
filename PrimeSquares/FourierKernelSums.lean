import PrimeSquares.FourierKernelAlgebra

open Finset
namespace PrimeSquares

theorem fourierKernel_zero (x : ℤ) : fourierKernel 0 x = 0 := by
  unfold fourierKernel fourierKernelSequence
  simp only [map_zero,lp.coeFn_zero,Pi.zero_apply]

theorem fourierKernel_sum {ι : Type*} (S : Finset ι)
    (m : ι → C(PrimeCircle, ℂ)) (x : ℤ) :
    fourierKernel (∑ i ∈ S, m i) x = ∑ i ∈ S, fourierKernel (m i) x := by
  unfold fourierKernel fourierKernelSequence
  rw [map_sum,map_sum,lp.coeFn_sum,Finset.sum_apply]

end PrimeSquares
