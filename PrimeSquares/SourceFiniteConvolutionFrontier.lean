import PrimeSquares.SourceHighOperatorFrontier
import PrimeSquares.CircleFiniteDecomposition
open scoped lp
namespace PrimeSquares
theorem annularConvolution_source_frontier (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hQR : Q ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x=
      circleLowOperator (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β (finiteInputLp F f 1) x+
      integerMultiplier (sourceCollarDifference N hN Q R q₀ active χ β) (finiteInputLp F f 2) x+
      integerMultiplier (sourceLargeHighRemainder N hN Q R q₀ active χ β) (finiteInputLp F f 2) x+
      circleMajorArcErrorOperator (sourceRationalCenters R) N hN χ (sourceExceptionalSelector q₀ active) β (finiteInputLp F f 2) x := by
  have hh := annularKernel_finite_low_high_error (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
    χ (sourceExceptionalSelector q₀ active) β F f x
  rw [circleHighOperator_collar_remainder N hN hQ hq₀ hQR] at hh
  simpa only [_root_.add_apply,lp.coeFn_add,Pi.add_apply,add_assoc] using hh
end PrimeSquares
