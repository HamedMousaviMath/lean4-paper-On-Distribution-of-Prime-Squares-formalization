import PrimeSquares.LocalizedIntervalSquareMaximum
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem circle_interval_majorants (m : ℕ → ℕ → C(PrimeCircle,ℂ)) (p : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ t i,m t i=m t i*p i) (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0)
    {B : ℝ} (hB : 0 ≤ B)
    (hE : ∀ k b,∀ J : Finset ℕ,∀ θ : PrimeCircle,
      (∑ t ∈ J,‖intervalCircleSymbol b (2^k) (m t) θ‖^2) ≤ B^2) (f : ℓ²(ℤ,ℂ)) :
    ∃ G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2,
      (∀ t k b x,‖integerMultiplier (intervalCircleSymbol b (2^k) (m t)) f x‖ ≤ G k b x) ∧
      (∀ k b,‖G k b‖ ≤ B*‖integerMultiplier (intervalCircleSymbol b (2^k) p) f‖) := by
  have hex (k b : ℕ) := localized_circle_square_maximum
    (fun t => intervalCircleSymbol b (2^k) (m t)) (intervalCircleSymbol b (2^k) p)
    (fun t => intervalCircleSymbol_localized b (2^k) (m t) p (hm t) hp) hB (hE k b) f
  choose G _hg ht hn using hex
  exact ⟨G,fun t k b x => ht k b t x,hn⟩
end PrimeSquares
