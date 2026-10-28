import PrimeSquares.NormalizedCohenCorrelation
import PrimeSquares.RealCutoffFloorBudget
import PrimeSquares.WeightedKernelAssembly

open Finset
namespace PrimeSquares

theorem realOrdinaryPhysicalKernel_decay {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q) (x : ℤ) :
    ‖realOrdinaryPhysicalKernel N Q x‖ ≤
      (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*
        decayProfile ((N : ℝ)^2) 10 x*((cohenLogConstant/2)*Real.log (2*Q)) := by
  have hC := cutoffDecayConstant_nonneg 10
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQp : (0 : ℝ) < Q := by linarith
  let B : ℝ := (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x
  have hB : 0 ≤ B := by dsimp [B];exact mul_nonneg (by positivity) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  calc
    _ ≤ B*∑ q ∈ Icc 1 ⌊Q⌋₊,‖normalizedCohenCorrelation q x‖*(q : ℝ)⁻¹ := by
      apply weighted_kernel_sum_bound
      intro q hq
      obtain ⟨hq1,hqQ⟩ := mem_Icc.mp hq
      have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have ha := ordinaryLowWidth_pos hNp hQp hqp
      have hle := ordinaryLowWidth_le_square (q := (q : ℝ)) hNp.le hQp (real_cutoff_denominator_bound hQp.le hqQ)
      have h := smoothedAnnularKernel_decay hN (by norm_num : (1 : ℝ) ≤ 1) ha hle 10 (x : ℝ)
      convert h using 1
      dsimp [B,ordinaryLowWidth]
      norm_num
      field_simp
      ring
    _ ≤ B*((cohenLogConstant/2)*Real.log (2*Q)) :=
      mul_le_mul_of_nonneg_left (by
        have h := normalizedCohenCorrelation_log ⌊Q⌋₊ (floor_cutoff_two hQ) x
        have hl := mul_le_mul_of_nonneg_left (floor_cutoff_log (by linarith : 1 ≤ Q))
          (div_nonneg cohenLogConstant_pos.le (by norm_num : (0 : ℝ) ≤ 2))
        simpa only [div_eq_mul_inv] using h.trans hl) hB
    _ = _ := rfl

end PrimeSquares
