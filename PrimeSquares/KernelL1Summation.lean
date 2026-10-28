import PrimeSquares.UniformFourierKernel

open MeasureTheory
open scoped lp
namespace PrimeSquares

noncomputable def kernelL1Sum (K : ℤ → ℂ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) : ℂ :=
  ∑' y : ℤ, K (x-y)*f y

theorem kernelL1_summable (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    Summable (fun y : ℤ => K (x-y)*f y) := by
  have hf : Summable (fun y : ℤ => ‖f y‖) := by simpa using f.2.summable
  exact (hf.mul_left B).of_norm_bounded fun y => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK (x-y)) (norm_nonneg _)

theorem kernelL1Sum_bound (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    ‖kernelL1Sum K f x‖ ≤ B*‖f‖ := by
  have hf : Summable (fun y : ℤ => ‖f y‖) := by simpa using f.2.summable
  calc
    _ ≤ ∑' y : ℤ, ‖K (x-y)*f y‖ := norm_tsum_le_tsum_norm (kernelL1_summable K hK f x).norm
    _ ≤ ∑' y : ℤ, B*‖f y‖ := by
      apply Summable.tsum_le_tsum
      · intro y
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hK (x-y)) (norm_nonneg _)
      · exact (kernelL1_summable K hK f x).norm
      · exact hf.mul_left B
    _ = B*‖f‖ := by
      rw [tsum_mul_left]
      congr 1
      rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
      simp

end PrimeSquares
