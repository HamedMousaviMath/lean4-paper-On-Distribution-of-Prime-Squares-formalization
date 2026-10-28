import PrimeSquares.LocalizedAnnularSource
import PrimeSquares.CompactCirclePeriodization
namespace PrimeSquares
noncomputable def circleAnnularSource (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) (r : ℚ) : C(PrimeCircle,ℂ) :=
  (compactCircleLift (localizedAnnularSource N hN β s)
    (localizedAnnularSource_support N hN β s)).comp
    ⟨fun θ => θ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩
theorem circleAnnularSource_real (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (s : ℕ) (r : ℚ) (ξ : ℝ) :
    circleAnnularSource N hN β s r (ξ : PrimeCircle)=
      ∑' k : ℤ,annularOscillatoryModel N β (ξ-(r : ℝ)+k)*
        Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  change compactCircleLift (localizedAnnularSource N hN β s)
    (localizedAnnularSource_support N hN β s)
    ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle)) = _
  rw [←AddCircle.coe_sub,compactCircleLift_all_real]
  rfl
end PrimeSquares
