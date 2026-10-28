import PrimeSquares.InducedWeightedCorrelation
import PrimeSquares.ExceptionalLowWidth
import PrimeSquares.WeightedKernelAssembly

open Finset
namespace PrimeSquares

noncomputable def exceptionalPhysicalLowKernel (N Q q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (S : Finset ℕ) (x : ℤ) : ℂ :=
  ∑ d ∈ S,inducedIntegerCorrelation q₀ χ₀ d x*
    smoothedAnnularKernel N β (exceptionalLowWidth N Q (conductorMajorant q₀) d) x

theorem exceptionalPhysicalLowKernel_decay {N Q : ℕ} (hN : 2 ≤ N) (hQ : 1 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (x : ℤ) :
    ‖exceptionalPhysicalLowKernel N Q q₀ χ₀ β S x‖ ≤
      (512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2)*
        decayProfile ((N : ℝ)^2) 10 x*(correlationLogConstant*Real.log (2*(Q : ℝ))) := by
  have hC := cutoffDecayConstant_nonneg 10
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hBp : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  let B : ℝ := (512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x
  have hB : 0 ≤ B := by dsimp [B];exact mul_nonneg (by positivity) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  calc
    _ ≤ B*∑ d ∈ S,conductorCorrelationProduct d/(d : ℝ) := by
      apply weighted_kernel_sum_majorant
      intro d hd
      have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d from (mem_Icc.mp (hS hd)).1)
      have ha := exceptionalLowWidth_pos hNp hQp hBp hdp
      have haN := exceptionalLowWidth_le_square (N := (N : ℝ)) hQp (hwidth d hd)
      have hs := smoothedAnnularKernel_decay hN hβ ha haN 10 (x : ℝ)
      have hc := inducedIntegerCorrelation_bound q₀ d χ₀ hχ x
      rw [norm_mul]
      have hp := mul_le_mul hc hs (norm_nonneg _) (mul_nonneg hBp.le
        ((by norm_num : (0 : ℝ) ≤ 1).trans (conductorCorrelationProduct_one_le d)))
      convert hp using 1
      dsimp [B,exceptionalLowWidth]
      norm_num
      field_simp
      ring
    _ ≤ B*(correlationLogConstant*Real.log (2*(Q : ℝ))) :=
      mul_le_mul_of_nonneg_left (conductorCorrelationProduct_subset_log S Q hQ hS) hB
    _ = _ := rfl

end PrimeSquares
