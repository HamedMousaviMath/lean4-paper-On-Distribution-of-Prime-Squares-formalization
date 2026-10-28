import PrimeSquares.LocalizedMultiplierEstimate
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem localized_symbol_cross (m p : ℕ → C(PrimeCircle,ℂ))
    (hm : ∀ i,m i=m i*p i) (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0)
    {i j : ℕ} (hij : i ≠ j) : m i*p j=0 := by
  ext θ
  change m i θ*p j θ=0
  rcases hp i j hij θ with hi|hj
  · have he := congrArg (fun z : C(PrimeCircle,ℂ) => z θ) (hm i)
    change m i θ=m i θ*p i θ at he
    rw [hi,mul_zero] at he
    rw [he,zero_mul]
  · rw [hj,mul_zero]
end PrimeSquares
