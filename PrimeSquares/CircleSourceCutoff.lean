import PrimeSquares.SourceCutoffContinuousMap
import PrimeSquares.CompactCirclePeriodization
namespace PrimeSquares
noncomputable def circleSourceCutoff (s : ℕ) (r : ℚ) : C(PrimeCircle,ℂ) :=
  (compactCircleLift (sourceCutoffContinuousMap s) (sourceCutoffContinuousMap_support s)).comp
    ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩
theorem circleSourceCutoff_real (s : ℕ) (r : ℚ) (ξ : ℝ) :
    circleSourceCutoff s r (ξ : PrimeCircle)=
      ∑' k : ℤ, Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  change compactCircleLift (sourceCutoffContinuousMap s) (sourceCutoffContinuousMap_support s)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [← AddCircle.coe_sub,compactCircleLift_all_real]
  rfl
end PrimeSquares
