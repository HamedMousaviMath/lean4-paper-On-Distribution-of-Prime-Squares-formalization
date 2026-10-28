import PrimeSquares.FiniteDecayConvolution

open Finset
namespace PrimeSquares

theorem finiteConvolution_outside_ball (K : ℤ → ℂ) {A H R : ℝ} (hA : 0 ≤ A) (hH : 0 < H)
    (hR : 0 ≤ R) (k : ℕ) (hK : ∀ z : ℤ, ‖K z‖ ≤ A*decayProfile H k z)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) (hF : ∀ y ∈ F, R ≤ |((x-y : ℤ) : ℝ)|) :
    ‖finiteConvolution K F f x‖ ≤ A*decayProfile H k R*∑ y ∈ F, ‖f y‖ := by
  have hk : ∀ y ∈ F, ‖K (x-y)‖ ≤ A*decayProfile H k R := by
    intro y hy
    exact (hK _).trans (mul_le_mul_of_nonneg_left
      (decayProfile_mono_abs hH k (by simpa only [abs_of_nonneg hR] using hF y hy)) hA)
  calc
    _ ≤ ∑ y ∈ F, ‖K (x-y)*f y‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ F, (A*decayProfile H k R)*‖f y‖ := by
      apply sum_le_sum;intro y hy;rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hk y hy) (norm_nonneg _)
    _ = _ := (mul_sum ..).symm

theorem finiteConvolution_split_ball (K : ℤ → ℂ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) (R : ℝ) :
    finiteConvolution K F f x =
      finiteConvolution K (F.filter (fun y => |((x-y : ℤ) : ℝ)| ≤ R)) f x+
      finiteConvolution K (F.filter (fun y => ¬|((x-y : ℤ) : ℝ)| ≤ R)) f x := by
  classical
  exact (Finset.sum_filter_add_sum_filter_not F _ _).symm

end PrimeSquares
