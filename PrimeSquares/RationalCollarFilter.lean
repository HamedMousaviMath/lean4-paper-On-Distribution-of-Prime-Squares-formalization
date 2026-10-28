import PrimeSquares.LargeCircleExceptionalHigh
open Finset
namespace PrimeSquares
theorem rationalCollarBlock_filter (Γ : Finset ℚ) (p : ℚ → Prop) [DecidablePred p]
    (N : ℕ) (hN : 1 ≤ N) (W : ℝ) (β : ℚ → ℝ) (c : ℚ → ℂ) :
    rationalCollarBlock (Γ.filter p) N hN W β c=
      rationalCollarBlock Γ N hN W β (fun r => if p r then c r else 0) := by
  unfold rationalCollarBlock
  rw [sum_filter]
  apply sum_congr rfl
  intro r _
  ext θ
  by_cases hp : p r <;> simp [hp,smul_eq_mul]
end PrimeSquares
