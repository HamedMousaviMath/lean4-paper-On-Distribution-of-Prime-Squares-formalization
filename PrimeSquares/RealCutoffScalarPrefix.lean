import PrimeSquares.RealDenominatorPrefixSet
open Finset
namespace PrimeSquares
theorem real_cutoff_scalar_prefix (L : ℕ) {R : ℝ} (hR : 0 ≤ R) (f : ℕ → ℂ) :
    (∑ q ∈ range L,denominatorActivation R q*f q)=intervalComplexSum 0 (min L (⌊R⌋₊+1)) f := by
  classical
  unfold intervalComplexSum
  rw [←real_denominator_prefix_filter L hR,sum_filter]
  simp only [denominatorActivation,Nat.zero_add]
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp
end PrimeSquares
