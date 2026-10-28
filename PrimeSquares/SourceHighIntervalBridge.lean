import PrimeSquares.SourceTimeBandFromIntervals
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceHigh_interval_bridge (M h : ℕ) (hM : M+1 ≤ 2^h)
    (N : ℕ → ℕ) (hN : ∀ t,1 ≤ N t) (q₀ : ℕ → ℕ) (Q B₀ : ℕ → ℝ)
    (χ : ∀ _t : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ)
    (f : ℓ²(ℤ,ℂ)) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2)
    (w : ℕ → ℝ) (hw : ∀ i,0 ≤ w i) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t k b x,‖integerMultiplier (intervalCircleSymbol b (2^k)
      (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleHighTerm (N t) (hN t) (q₀ t) (Q t) (B₀ t) (χ t) (κ t) (β t)))) f x‖ ≤ G k b x)
    (hI : ∀ k b,‖G k b‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t R,0 ≤ R → ∀ x,‖circleHighOperator
        ((sourceRationalCenters R).filter (fun r => r.den ≤ M))
        (N t) (hN t) (q₀ t) (Q t) (B₀ t) (χ t) (κ t) (β t) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget 0 (2^h) w) := by
  exact source_time_prefix_from_intervals M h hM
    (fun t => circleHighTerm (N t) (hN t) (q₀ t) (Q t) (B₀ t) (χ t) (κ t) (β t))
    f G w hw hB hG hI
end PrimeSquares
