import PrimeSquares.PrimeSquareAverages

open Finset
namespace PrimeSquares

theorem mangoldtSquareKernel_cutoff_bound {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) (z : ℤ) :
    ‖weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt z‖ ≤
      ((M : ℝ)/(N : ℝ))*(weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt z).re := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hN hNM
  have hKM : NonnegativeKernel (weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt) :=
    finiteSquareKernel_nonnegative _ (by positivity) _ (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  by_cases hz : z ∈ (Ioc 0 N).image (fun n : ℕ => (n : ℤ)^2)
  · obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
    have hnM : n ∈ Ioc 0 M := mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hNM⟩
    simp only [weightedSquareAverageKernel,finiteSquareKernel_at_square,ite_eq_left hn,ite_eq_left hnM]
    rw [←Complex.ofReal_mul,Complex.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hNr.le) ArithmeticFunction.vonMangoldt_nonneg)]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    apply le_of_eq
    field_simp
  · change ‖finiteSquareKernel (Ioc 0 N) (N : ℝ)⁻¹ ArithmeticFunction.vonMangoldt z‖ ≤ _
    rw [finiteSquareKernel_eq_zero _ _ _ hz,norm_zero]
    exact mul_nonneg (div_nonneg hMr.le hNr.le) (hKM z).2

theorem mangoldtSquarePairing_cutoff_bound {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖ ≤
      ((M : ℝ)/(N : ℝ))*‖restrictedKernelPairing (weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt) F G‖ := by
  have hKM : NonnegativeKernel (weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt) :=
    finiteSquareKernel_nonnegative _ (by positivity) _ (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  apply restrictedKernelPairing_domination hKM ((M : ℝ)/(N : ℝ))
  intro F x
  calc
    _ ≤ ∑ y ∈ F,‖weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt (x-y)‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ F,((M : ℝ)/(N : ℝ))*(weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt (x-y)).re :=
      sum_le_sum (fun y _ => mangoldtSquareKernel_cutoff_bound hN hNM (x-y))
    _ = _ := by simp only [indicatorConvolution,Complex.re_sum,mul_sum]

theorem exists_dyadic_upper_nat (N : ℕ) (hN : 0 < N) :
    ∃ k : ℕ,N ≤ 2^k ∧ 2^k ≤ 2*N := by
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨k+1,?_,?_⟩
  · have hNr : (N : ℝ) ≤ (2 : ℝ)^(k+1) := hk'.le
    exact_mod_cast hNr
  · have hNat : (2 : ℕ)^k ≤ N := by exact_mod_cast hk
    rw [pow_succ]
    omega

end PrimeSquares
