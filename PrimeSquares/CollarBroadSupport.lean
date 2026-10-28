import PrimeSquares.CollarBroadSymbol

namespace PrimeSquares

theorem annularCollarSymbol_zero_of_broad (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (θ : ℝ)
    (hz : sourceArcCutoffScale s θ=0) : annularCollarSymbol N hN β q Q s θ=0 := by
  simp only [annularCollarSymbol,ContinuousMap.coe_mk,hz,Complex.ofReal_zero,mul_zero]

theorem annularCollarSymbol_support (N : ℕ) (hN : 1 ≤ N) (β q Q : ℝ) (s : ℕ) (θ : ℝ)
    (hθ : 1 ≤ |θ|) : annularCollarSymbol N hN β q Q s θ=0 :=
  annularCollarSymbol_zero_of_broad N hN β q Q s θ (sourceArcCutoffScale_zero_of_unit s hθ)

end PrimeSquares
