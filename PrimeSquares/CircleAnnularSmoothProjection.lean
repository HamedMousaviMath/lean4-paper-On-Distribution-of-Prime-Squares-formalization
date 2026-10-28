import PrimeSquares.LocalizedAnnularSmoothProjection
namespace PrimeSquares
noncomputable def circleAnnularSmoothProjection (N s : ℕ) (r : ℚ) : C(PrimeCircle,ℂ) :=
  (compactCircleLift (localizedAnnularSmoothProjection N s)
    (localizedAnnularSmoothProjection_support N s)).comp
    ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩
theorem circleAnnularSmoothProjection_real (N s : ℕ) (r : ℚ) (ξ : ℝ) :
    circleAnnularSmoothProjection N s r (ξ : PrimeCircle)=
      ∑' k : ℤ,Complex.ofReal (sourceArcCutoff ((N : ℝ)^2*(ξ-(r : ℝ)+k)))*
        Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  change compactCircleLift (localizedAnnularSmoothProjection N s)
    (localizedAnnularSmoothProjection_support N s)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [←AddCircle.coe_sub,compactCircleLift_all_real]
  rfl
end PrimeSquares
