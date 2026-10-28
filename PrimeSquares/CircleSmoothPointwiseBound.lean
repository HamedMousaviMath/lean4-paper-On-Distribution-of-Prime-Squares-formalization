import PrimeSquares.CircleSmoothLiftValue
namespace PrimeSquares
theorem circleSmoothCutoff_pointwise_norm {a : ℝ} (ha : 1 ≤ a) (h4 : 4 ≤ a) (r : ℚ) (θ : PrimeCircle) :
    ‖circleSmoothCutoff a ha r θ‖ ≤ 1 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he]
  by_cases hz : circleSmoothCutoff a ha r (ξ : PrimeCircle)=0
  · simp [hz]
  · have hk : ∃ k : ℤ,sourceArcCutoff (a*(ξ-(r : ℝ)+k)) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hz
      rw [circleSmoothCutoff_real]
      simp only [hn,Complex.ofReal_zero,tsum_zero]
    obtain ⟨k,hk⟩ := hk
    rw [circleSmoothCutoff_eq_lift ha h4 r ξ k hk,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact sourceArcCutoff_le_one _
end PrimeSquares
