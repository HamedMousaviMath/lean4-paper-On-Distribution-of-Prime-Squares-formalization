import PrimeSquares.SourceLowFullRange

namespace PrimeSquares

theorem sourceFullLow_L1_norm {N : ℕ} (hN : 2 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (active : Bool) {β : ℝ} (hβ : β ≤ 1)
    {Q R : ℝ} (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2) :
    ‖fourierL1Operator (circleLowModel (sourceRationalCenters R) N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β)‖ ≤ 2*realLowAmplitude N Q := by
  rw [sourceFullLow_squared (by omega) q₀ χ₀ active β (by linarith) hQR hb]
  exact realCombinedLowModel_L1_norm hN hQ _ q₀ χ₀ hχ hβ ⌊R⌋₊ active

theorem sourceFullLow_local {N : ℕ} (hN : 2 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (active : Bool) {β : ℝ} (hβ : β ≤ 1)
    {Q R : ℝ} (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖integerMultiplier (circleLowModel (sourceRationalCenters R) N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β) (finiteInputLp F f 2) x‖ ≤
      (8*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  rw [sourceFullLow_squared (by omega) q₀ χ₀ active β (by linarith) hQR hb]
  exact realCombinedLowModel_local hN hQ _ q₀ χ₀ hχ hβ ⌊R⌋₊ active F f x

theorem sourceFullLow_kernel_decay {N : ℕ} (hN : 2 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (active : Bool) {β : ℝ} (hβ : β ≤ 1)
    {Q R : ℝ} (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^8 ≤ (N : ℝ)^2) (x : ℤ) :
    ‖fourierKernel (circleLowModel (sourceRationalCenters R) N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β) x‖ ≤
      2*realLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x := by
  rw [sourceFullLow_squared (by omega) q₀ χ₀ active β (by linarith) hQR hb,realCombinedLowModel_kernel]
  exact realCombinedPhysicalKernel_decay hN hQ q₀ χ₀ hχ hβ ⌊R⌋₊ active x

end PrimeSquares
