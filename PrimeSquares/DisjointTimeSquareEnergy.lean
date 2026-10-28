import PrimeSquares.TimeClassFiniteSum
open Finset
namespace PrimeSquares
theorem disjoint_time_square_energy (u : ℕ → ℕ → ℂ) (B : ℕ → ℝ)
    (hE : ∀ i,∀ I : Finset ℕ,(∑ j ∈ I,‖u j i‖^2) ≤ (B i)^2)
    (σ : ℕ → ℕ) (J : Finset ℕ) :
    (∑ j ∈ J,‖u j (σ j)‖^2) ≤ ∑ i ∈ J.image σ,(B i)^2 := by
  classical
  rw [time_class_sum J σ]
  apply sum_le_sum
  intro i _
  calc
    _ = ∑ j ∈ J.filter (fun j => σ j=i),‖u j i‖^2 :=
      sum_congr rfl (fun j hj => by rw [(mem_filter.mp hj).2])
    _ ≤ _ := hE i _
end PrimeSquares
