import PrimeSquares.CircleSourceCutoffLiftValue
import PrimeSquares.CircleSourceCutoffWitness
namespace PrimeSquares
theorem circleSourceCutoff_pointwise_norm {s : ℕ} (hs : 1 ≤ s) (r : ℚ) (θ : PrimeCircle) :
    ‖circleSourceCutoff s r θ‖ ≤ 1 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [← he]
  by_cases hz : circleSourceCutoff s r (ξ : PrimeCircle)=0
  · simp [hz]
  · obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hz
    rw [circleSourceCutoff_eq_lift hs r ξ k hk,Complex.norm_real,Real.norm_eq_abs]
    have hp : 0 ≤ sourceArcCutoffScale s (ξ-(r : ℝ)+k) := sourceArcCutoff_nonneg _
    rw [abs_of_nonneg hp]
    exact sourceArcCutoff_le_one _
end PrimeSquares
