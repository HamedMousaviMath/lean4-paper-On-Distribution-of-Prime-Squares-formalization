import PrimeSquares.WeightedSourceCutoffInput
import PrimeSquares.SourceSmoothCrossProduct
import PrimeSquares.SmoothProjectionCircleFactorization
open Finset
namespace PrimeSquares
theorem weightedSmoothSource_factorization {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (c : ℚ → ℂ) (ha : 1 ≤ (N : ℝ)^2) (hscale : (16 : ℝ)^s ≤ (N : ℝ)^2) :
    weightedSourceCutoff Γ s c*(∑ t ∈ Γ,circleSmoothCutoff ((N : ℝ)^2) ha t)=
      ∑ r ∈ Γ,c r • circleAnnularSmoothProjection N s r := by
  classical
  unfold weightedSourceCutoff
  rw [sum_mul]
  apply sum_congr rfl
  intro r hr
  rw [mul_sum,sum_eq_single r]
  · rw [circleAnnularSmoothProjection_factorization hN (by omega) r ha]
    ext θ
    simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring
  · intro t ht htr
    rw [smul_mul_assoc,source_smooth_cross_product hs ha hscale (hc r hr) (hc t ht)
      htr.symm (hd r hr) (hd t ht)]
    ext θ
    simp
  · exact fun hn => (hn hr).elim
end PrimeSquares
