import PrimeSquares.CircleTimePrefixMaximum
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem circle_time_prefix_pairing (h a : ℕ) (m : ℕ → ℕ → C(PrimeCircle,ℂ))
    (p : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ t i,m t i=m t i*p i) (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0)
    {B : ℝ} (hB : 0 ≤ B)
    (hE : ∀ k b,∀ J : Finset ℕ,∀ θ : PrimeCircle,
      (∑ t ∈ J,‖intervalCircleSymbol b (2^k) (m t) θ‖^2) ≤ B^2)
    (f : ℓ²(ℤ,ℂ)) (S : Finset ℤ) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ t K,K ≤ 2^h → ∀ x,‖integerMultiplier (intervalCircleSymbol a K (m t)) f x‖ ≤ g x) ∧
      (∑ x ∈ S,g x) ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h)
        (fun i => ‖integerMultiplier (p i) f‖^2))*Real.sqrt S.card := by
  obtain ⟨g,hg,ht,hn⟩ := circle_time_prefix_maximum h a m p hm hp hB hE f
  exact ⟨g,ht,(real_l2_finite_sum_bound S g (fun x _ => hg x)).trans
    (mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _))⟩
end PrimeSquares
