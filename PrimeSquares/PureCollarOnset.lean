import PrimeSquares.PureCollarMask

namespace PrimeSquares

theorem annularCollarMask_onset {N q Q θ : ℝ} (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (hn : annularCollarMask N q Q θ ≠ 0) : Q/(2*q*N^2) < |θ| := by
  apply ordinary_collar_frequency_lower (b := 1) hQ hq hN (by ring)
  exact hn

theorem annularCollarMask_zero_of_core {N q Q θ : ℝ} (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (hθ : |θ| ≤ Q/(2*q*N^2)) : annularCollarMask N q Q θ=0 := by
  by_contra hn
  exact (not_lt_of_ge hθ) (annularCollarMask_onset hN hq hQ hn)

end PrimeSquares
