import PrimeSquares.SeparatedSmoothCircleNorm
import PrimeSquares.FiniteMultiplierMaximalCriterion
open scoped lp
namespace PrimeSquares
noncomputable def circleFrequencyLogFactor (Γ : Finset ℚ) : ℝ :=
  (1+Real.log ((Γ.card : ℝ)+1))^2
theorem circleFrequencyLogFactor_nonneg (Γ : Finset ℚ) : 0 ≤ circleFrequencyLogFactor Γ :=
  sq_nonneg _
/-- Unproved external analytic boundary: smooth multifrequency theory, sampling,
normalization and the fixed source bump. This definition is not a theorem or axiom. -/
def SmoothCircleBourgainInput (C : ℝ) : Prop :=
  ∀ Γ : Finset ℚ,(∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) →
  ∀ δ : ℝ,0<δ → δ≤1 → PeriodicFrequencySeparated Γ δ →
  ∀ (a : ℝ) (ha : 4≤a),16≤a*δ →
  ∀ J : Finset ℕ,∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
    (∀ j ∈ J,∀ x,‖integerMultiplier (unweightedSmoothCircleFamily Γ a ha j) f x‖≤g x) ∧
    ‖g‖≤C*circleFrequencyLogFactor Γ*‖f‖
theorem smoothCircleBourgain_countable {C : ℝ} (hC : 0≤C) (h : SmoothCircleBourgainInput C)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) (hsep : PeriodicFrequencySeparated Γ δ)
    (a : ℝ) (ha : 4≤a) (hscale : 16≤a*δ) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (unweightedSmoothCircleFamily Γ a ha j) f x‖≤g x) ∧
      ‖g‖≤C*circleFrequencyLogFactor Γ*‖f‖ :=
  finite_multiplier_countable_maximum _ (mul_nonneg hC (circleFrequencyLogFactor_nonneg Γ))
    (h Γ hc δ hδ hδ1 hsep a ha hscale) f
end PrimeSquares
