import PrimeSquares.SmoothProjectionSourceSupport
import PrimeSquares.SmoothProjectionLiftValue
import PrimeSquares.SmoothCutoffSourceLiftCompatibility
import PrimeSquares.CircleSourceCutoffLiftValue
import PrimeSquares.CircleSourceCutoffWitness
namespace PrimeSquares
theorem circleAnnularSmoothProjection_factorization {N : ℕ} (hN : 2 ≤ N) {s : ℕ} (hs : 1 ≤ s)
    (r : ℚ) (ha : 1 ≤ (N : ℝ)^2) :
    circleAnnularSmoothProjection N s r=circleSmoothCutoff ((N : ℝ)^2) ha r*circleSourceCutoff s r := by
  ext θ
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (4 : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  change circleAnnularSmoothProjection N s r θ=circleSmoothCutoff ((N : ℝ)^2) ha r θ*circleSourceCutoff s r θ
  rw [←he]
  by_cases hz : circleSourceCutoff s r (ξ : PrimeCircle)=0
  · rw [circleAnnularSmoothProjection_cutoff_zero N hs r _ hz,hz,mul_zero]
  · obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hz
    rw [circleAnnularSmoothProjection_eq_lift N hs r ξ k hk,
      circleSmoothCutoff_on_source_lift ha h4 hs r ξ k hk,circleSourceCutoff_eq_lift hs r ξ k hk]
end PrimeSquares
