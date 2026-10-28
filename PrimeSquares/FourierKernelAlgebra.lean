import PrimeSquares.FourierKernels

namespace PrimeSquares

theorem fourierKernel_add (m n : C(PrimeCircle, ℂ)) (x : ℤ) :
    fourierKernel (m+n) x = fourierKernel m x + fourierKernel n x := by
  unfold fourierKernel fourierKernelSequence
  rw [map_add, map_add, lp.coeFn_add, Pi.add_apply]

theorem fourierKernel_smul (c : ℂ) (m : C(PrimeCircle, ℂ)) (x : ℤ) :
    fourierKernel (c • m) x = c*fourierKernel m x := by
  unfold fourierKernel fourierKernelSequence
  rw [map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

theorem fourierKernel_sub (m n : C(PrimeCircle, ℂ)) (x : ℤ) :
    fourierKernel (m-n) x = fourierKernel m x - fourierKernel n x := by
  rw [sub_eq_add_neg, fourierKernel_add, ← neg_one_smul ℂ n, fourierKernel_smul]
  ring

end PrimeSquares
