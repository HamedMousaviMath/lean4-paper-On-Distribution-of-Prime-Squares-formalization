import PrimeSquares.SquareMaximalTailBounds

open Filter
open scoped lp Topology
namespace PrimeSquares

theorem squareMaximum_tail_norm_zero (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Tendsto (fun J : ℕ => ‖squareMaximumL2 (fun j => F (J+j)) (square_tail_summable F hF J)‖) atTop (𝓝 0) := by
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp (tendsto_sum_nat_add (fun j : ℕ => ‖F j‖^2))
  have he : Tendsto (fun J : ℕ => Real.sqrt (∑' j : ℕ,‖F (J+j)‖^2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.add_comm,Real.sqrt_zero] using ht
  exact squeeze_zero (fun J => norm_nonneg _) (fun J => squareMaximum_tail_norm F hF J) he

theorem squareMaximum_tail_zero (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Tendsto (fun J : ℕ => squareMaximumL2 (fun j => F (J+j)) (square_tail_summable F hF J)) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (squareMaximum_tail_norm_zero F hF)

end PrimeSquares
