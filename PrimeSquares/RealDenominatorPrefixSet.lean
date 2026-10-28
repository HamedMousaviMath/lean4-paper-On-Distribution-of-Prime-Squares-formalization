import PrimeSquares.FiniteNaturalPrefixSet
open Finset
namespace PrimeSquares
theorem real_denominator_prefix_filter (L : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (range L).filter (fun q : ℕ => (q : ℝ) ≤ R)=range (min L (⌊R⌋₊+1)) := by
  have he (q : ℕ) : (q : ℝ) ≤ R ↔ q ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR).symm
  simp_rw [he]
  exact natural_prefix_filter L ⌊R⌋₊
end PrimeSquares
