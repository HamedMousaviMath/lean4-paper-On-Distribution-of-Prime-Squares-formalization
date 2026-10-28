import PrimeSquares.SourceSmoothCrossLiftUniqueness
import PrimeSquares.CircleSourceCutoffWitness
namespace PrimeSquares
theorem source_smooth_cross_product {s : ℕ} (hs : 2 ≤ s) {a : ℝ} (ha1 : 1 ≤ a)
    (ha : (16 : ℝ)^s ≤ a) {r t : ℚ}
    (hr : r ∈ Set.Ico (0 : ℚ) 1) (ht : t ∈ Set.Ico (0 : ℚ) 1) (hne : r ≠ t)
    (hrD : (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (htD : (t.den : ℝ) ≤ (2 : ℝ)^(s+1)) :
    circleSourceCutoff s r*circleSmoothCutoff a ha1 t=0 := by
  ext θ
  change circleSourceCutoff s r θ*circleSmoothCutoff a ha1 t θ=0
  by_cases hz : circleSourceCutoff s r θ=0
  · simp only [hz,zero_mul]
  by_cases hw : circleSmoothCutoff a ha1 t θ=0
  · simp only [hw,mul_zero]
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he] at hz hw
  obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift ξ hz
  obtain ⟨l,hl⟩ := circleSmoothCutoff_nonzero_lift ha1 t ξ hw
  exact (hne (source_smooth_cross_lift_unique hs ha hr ht hrD htD ξ k l hk hl)).elim
end PrimeSquares
