import PrimeSquares.TemporalMaximumMembership
open scoped lp
namespace PrimeSquares
theorem temporalMaximumL2_norm (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : FiniteTemporalMajorants F B) : ‖temporalMaximumL2 F hB hF‖ ≤ B := by
  have he : ‖temporalMaximumL2 F hB hF‖^2 ≤ B^2 := by
    rw [←real_l2_square_total]
    exact Real.tsum_le_of_sum_le (fun x => sq_nonneg _) (temporalMaximum_finite_spatial_energy F hB hF)
  have hn := norm_nonneg (temporalMaximumL2 F hB hF)
  nlinarith
end PrimeSquares
