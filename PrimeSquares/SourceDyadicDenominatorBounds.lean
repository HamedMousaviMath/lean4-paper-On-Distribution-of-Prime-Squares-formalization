import PrimeSquares.SourceDyadicRationalCenters
namespace PrimeSquares
theorem sourceDyadicRationalCenters_den_bounds {s : ℕ} {r : ℚ}
    (hr : r ∈ sourceDyadicRationalCenters s) :
    (2 : ℝ)^s ≤ r.den ∧ (r.den : ℝ) < (2 : ℝ)^(s+1) := by
  have hs := ((mem_sourceDyadicRationalCenters s r).mp hr).2
  have hb := (Nat.log2_eq_iff r.den_pos.ne').mp hs
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2
end PrimeSquares
