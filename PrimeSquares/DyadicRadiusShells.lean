import PrimeSquares.DyadicRadiusCover

namespace PrimeSquares

theorem dyadicRadiusLevel_zero_iff (H : ℝ) (hH : 0 < H) (d : ℝ) :
    dyadicRadiusLevel H hH d=0 ↔ |d| ≤ H := by
  constructor
  · intro h
    simpa only [h,pow_zero,one_mul] using dyadicRadiusLevel_upper H hH d
  · intro h
    apply Nat.le_zero.mp
    exact Nat.find_min' _ (by simpa only [pow_zero,one_mul] using h)

theorem dyadicRadiusLevel_succ_bounds (H : ℝ) (hH : 0 < H) (d : ℝ) (j : ℕ)
    (hj : dyadicRadiusLevel H hH d=j+1) :
    (2 : ℝ)^j*H < |d| ∧ |d| ≤ (2 : ℝ)^(j+1)*H := by
  constructor
  · exact dyadicRadiusLevel_minimal H hH d j (by omega)
  · simpa only [hj] using dyadicRadiusLevel_upper H hH d

end PrimeSquares
