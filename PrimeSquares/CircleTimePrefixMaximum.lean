import PrimeSquares.CircleIntervalMajorants
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem circle_time_prefix_maximum (h a : ℕ) (m : ℕ → ℕ → C(PrimeCircle,ℂ))
    (p : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ t i,m t i=m t i*p i) (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0)
    {B : ℝ} (hB : 0 ≤ B)
    (hE : ∀ k b,∀ J : Finset ℕ,∀ θ : PrimeCircle,
      (∑ t ∈ J,‖intervalCircleSymbol b (2^k) (m t) θ‖^2) ≤ B^2) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t K,K ≤ 2^h → ∀ x,‖integerMultiplier (intervalCircleSymbol a K (m t)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h)
        (fun i => ‖integerMultiplier (p i) f‖^2)) := by
  obtain ⟨G,hG,hI⟩ := circle_interval_majorants m p hm hp hB hE f
  apply localized_time_prefix_majorant h a m p hp f G hB hG
  intro k b
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hI k b) 2
end PrimeSquares
