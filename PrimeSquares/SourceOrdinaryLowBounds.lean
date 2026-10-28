import PrimeSquares.SourceOrdinaryLowIdentity
import PrimeSquares.RealOrdinaryL1Bound
import PrimeSquares.RealOrdinaryLocalOperator

namespace PrimeSquares

theorem sourceLowModel_no_exception_L1 {N : ℕ} (hN : 2 ≤ N) {Q R : ℝ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^4 ≤ (N : ℝ)^2) (q₀ : ℕ) (B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    ‖fourierL1Operator (circleLowModel (sourceRationalCenters R) N (by omega) q₀ Q B₀ χ (fun _ => 0) β)‖ ≤
      realLowAmplitude N Q := by
  rw [sourceLowModel_no_exception (by omega) (by linarith) hQR hb q₀ B₀ χ β]
  exact realOrdinaryLowModel_L1_norm hN hQ _

theorem sourceLowModel_no_exception_local {N : ℕ} (hN : 2 ≤ N) {Q R : ℝ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^4 ≤ (N : ℝ)^2) (q₀ : ℕ) (B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖integerMultiplier (circleLowModel (sourceRationalCenters R) N (by omega) q₀ Q B₀ χ (fun _ => 0) β)
      (finiteInputLp F f 2) x‖ ≤
      (4*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  rw [sourceLowModel_no_exception (by omega) (by linarith) hQR hb q₀ B₀ χ β]
  exact realOrdinaryLowModel_local hN hQ _ F f x

end PrimeSquares
