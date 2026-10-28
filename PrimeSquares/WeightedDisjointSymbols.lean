import PrimeSquares.IntervalIntegerMultiplier
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem weighted_symbols_disjoint (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i j,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) (c : ℕ → ℂ) :
    ∀ i j,i ≠ j → ∀ θ,(c i • m i) θ=0 ∨ (c j • m j) θ=0 := by
  intro i j hij θ
  rcases hm i j hij θ with hi|hj
  · exact Or.inl (by simp [hi])
  · exact Or.inr (by simp [hj])
end PrimeSquares
