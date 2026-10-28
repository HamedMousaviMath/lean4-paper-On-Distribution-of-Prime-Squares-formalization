import PrimeSquares.InducedWeightedCorrelation
import PrimeSquares.RealExceptionalLowModel
import PrimeSquares.RealCutoffFloorBudget
import PrimeSquares.WeightedKernelAssembly

open Finset
namespace PrimeSquares

theorem realExceptionalPhysicalKernel_decay {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (x : ℤ) :
    ‖realExceptionalPhysicalKernel N q₀ χ₀ Q β M x‖ ≤
      (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*
        decayProfile ((N : ℝ)^2) 10 x*(correlationLogConstant*Real.log (2*Q)) := by
  have hC := cutoffDecayConstant_nonneg 10
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQp : (0 : ℝ) < Q := by linarith
  have hBp : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  let S := realExceptionalDenominators q₀ M Q
  have hS : S ⊆ Icc 1 ⌊Q⌋₊ := realExceptionalDenominators_subset q₀ M Q
  have hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q := fun d hd =>
    ((mem_realExceptionalDenominators (NeZero.pos q₀) Q).mp hd).2.1
  let B : ℝ := (512*cutoffDecayConstant 10*Q/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x
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
    _ ≤ B*(correlationLogConstant*Real.log (2*Q)) :=
      mul_le_mul_of_nonneg_left (by
        have h := conductorCorrelationProduct_subset_log S ⌊Q⌋₊ (by have hf := floor_cutoff_two hQ;omega) hS
        have hl : Real.log (2*(⌊Q⌋₊ : ℝ)) ≤ Real.log (2*Q) :=
          Real.log_le_log (by have hf := floor_cutoff_two hQ;positivity)
            (mul_le_mul_of_nonneg_left (Nat.floor_le hQp.le) (by norm_num : (0 : ℝ) ≤ 2))
        exact h.trans (mul_le_mul_of_nonneg_left hl correlationLogConstant_pos.le)) hB
    _ = _ := rfl

end PrimeSquares
