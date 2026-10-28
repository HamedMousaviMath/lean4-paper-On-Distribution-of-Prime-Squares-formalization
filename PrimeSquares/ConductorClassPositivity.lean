import PrimeSquares.DisjointTimeSquareEnergy
namespace PrimeSquares
theorem conductor_class_positive (q₀ : ℕ → ℕ) (hclass : ∀ i,2^i ≤ q₀ i) (i : ℕ) : 0 < q₀ i :=
  (pow_pos (by norm_num : 0 < (2 : ℕ)) i).trans_le (hclass i)
theorem conductor_class_real_lower (q₀ : ℕ → ℕ) (hclass : ∀ i,2^i ≤ q₀ i) (i : ℕ) :
    (2 : ℝ)^i ≤ q₀ i := by exact_mod_cast hclass i
end PrimeSquares
