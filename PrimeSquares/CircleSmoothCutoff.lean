import PrimeSquares.ScaledSmoothCutoffMap
namespace PrimeSquares
noncomputable def circleSmoothCutoff (a : ℝ) (ha : 1 ≤ a) (r : ℚ) : C(PrimeCircle,ℂ) :=
  (compactCircleLift (scaledSmoothCutoffMap a) (scaledSmoothCutoffMap_support a ha)).comp
    ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩
theorem circleSmoothCutoff_real (a : ℝ) (ha : 1 ≤ a) (r : ℚ) (ξ : ℝ) :
    circleSmoothCutoff a ha r (ξ : PrimeCircle)=
      ∑' k : ℤ,Complex.ofReal (sourceArcCutoff (a*(ξ-(r : ℝ)+k))) := by
  change compactCircleLift (scaledSmoothCutoffMap a) (scaledSmoothCutoffMap_support a ha)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [←AddCircle.coe_sub,compactCircleLift_all_real]
  rfl
end PrimeSquares
