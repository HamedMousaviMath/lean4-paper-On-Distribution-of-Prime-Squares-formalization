import PrimeSquares.LocalizedCrossProducts
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem intervalCircleSymbol_localized (a K : ℕ) (m p : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i,m i=m i*p i) (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0) :
    intervalCircleSymbol a K m=intervalCircleSymbol a K m*intervalCircleSymbol a K p := by
  classical
  unfold intervalCircleSymbol
  symm
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  calc
    _ = m (a+i)*p (a+i) := by
      apply sum_eq_single i
      · intro j _ hji
        exact localized_symbol_cross m p hm hp (by omega : a+i ≠ a+j)
      · exact fun h => (h hi).elim
    _ = _ := (hm (a+i)).symm
end PrimeSquares
