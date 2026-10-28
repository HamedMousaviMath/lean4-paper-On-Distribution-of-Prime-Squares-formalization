import PrimeSquares.PaddedCircleSymbols
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem paddedCircleSymbols_disjoint (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i<L,∀ j<L,i ≠ j → ∀ θ,m i θ=0 ∨ m j θ=0) :
    ∀ i j,i ≠ j → ∀ θ,paddedCircleSymbols L m i θ=0 ∨ paddedCircleSymbols L m j θ=0 := by
  intro i j hij θ
  by_cases hi : i<L
  · by_cases hj : j<L
    · simpa [paddedCircleSymbols,hi,hj] using hm i hi j hj hij θ
    · exact Or.inr (by simp [paddedCircleSymbols,hj])
  · exact Or.inl (by simp [paddedCircleSymbols,hi])
end PrimeSquares
