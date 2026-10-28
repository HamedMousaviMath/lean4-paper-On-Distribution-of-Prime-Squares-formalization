import PrimeSquares.CollarPowerSummation
import PrimeSquares.DyadicDenominatorPartition

open Finset
namespace PrimeSquares

theorem rationalCollarBlock_dyadic_partition (Γ : Finset ℚ) (D N : ℕ) (hN : 1 ≤ N)
    (hden : ∀ r ∈ Γ,r.den ≤ D) (Q : ℝ) (β : ℚ → ℝ) (c : ℚ → ℂ) :
    rationalCollarBlock Γ N hN Q β c=
      ∑ s ∈ range (Nat.log2 D+1),rationalCollarBlock (Γ.filter (fun r => Nat.log2 r.den=s)) N hN Q β c := by
  classical
  exact rational_dyadic_partition Γ D hden
    (fun r => c r • circleAnnularCollar N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (r : ℝ))

end PrimeSquares
