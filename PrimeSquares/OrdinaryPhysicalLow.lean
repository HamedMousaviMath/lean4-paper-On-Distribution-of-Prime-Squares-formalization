import PrimeSquares.NormalizedCohenCorrelation
import PrimeSquares.OrdinaryLowWidth
import PrimeSquares.WeightedKernelAssembly

open Finset
namespace PrimeSquares

noncomputable def ordinaryPhysicalLowKernel (N Q : ℕ) (x : ℤ) : ℂ :=
  ∑ q ∈ Icc 1 Q,normalizedCohenCorrelation q x*
    smoothedAnnularKernel N 1 (ordinaryLowWidth N Q q) x

theorem ordinaryPhysicalLowKernel_decay {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q) (x : ℤ) :
    ‖ordinaryPhysicalLowKernel N Q x‖ ≤
      (512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2)*
        decayProfile ((N : ℝ)^2) 10 x*((cohenLogConstant/2)*Real.log ((Q : ℝ)+1)) := by
  have hC := cutoffDecayConstant_nonneg 10
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  let B : ℝ := (512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x
  have hB : 0 ≤ B := by dsimp [B];exact mul_nonneg (by positivity) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  calc
    _ ≤ B*∑ q ∈ Icc 1 Q,‖normalizedCohenCorrelation q x‖*(q : ℝ)⁻¹ := by
      apply weighted_kernel_sum_bound
      intro q hq
      obtain ⟨hq1,hqQ⟩ := mem_Icc.mp hq
      have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have ha := ordinaryLowWidth_pos hNp hQp hqp
      have hle := ordinaryLowWidth_le_square (q := (q : ℝ)) hNp.le hQp (by exact_mod_cast hqQ)
      have h := smoothedAnnularKernel_decay hN (by norm_num : (1 : ℝ) ≤ 1) ha hle 10 (x : ℝ)
      convert h using 1
      dsimp [B,ordinaryLowWidth]
      norm_num
      field_simp
      ring
    _ ≤ B*((cohenLogConstant/2)*Real.log ((Q : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (by simpa only [div_eq_mul_inv] using normalizedCohenCorrelation_log Q hQ x) hB
    _ = _ := rfl

end PrimeSquares
