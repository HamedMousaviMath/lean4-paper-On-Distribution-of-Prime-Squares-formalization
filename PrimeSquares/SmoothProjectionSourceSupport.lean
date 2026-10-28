import PrimeSquares.CircleAnnularSmoothProjection
import PrimeSquares.CircleSourceCutoffSupport
namespace PrimeSquares
theorem circleAnnularSmoothProjection_cutoff_zero (N : ℕ) {s : ℕ} (hs : 1 ≤ s)
    (r : ℚ) (θ : PrimeCircle) (hz : circleSourceCutoff s r θ=0) :
    circleAnnularSmoothProjection N s r θ=0 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he] at hz ⊢
  have hb (k : ℤ) : sourceArcCutoffScale s (ξ-(r : ℝ)+k)=0 := by
    by_contra hk
    exact circleSourceCutoff_ne_zero_of_lift hs r ξ k hk hz
  rw [circleAnnularSmoothProjection_real]
  simp only [hb,Complex.ofReal_zero,mul_zero,tsum_zero]
end PrimeSquares
