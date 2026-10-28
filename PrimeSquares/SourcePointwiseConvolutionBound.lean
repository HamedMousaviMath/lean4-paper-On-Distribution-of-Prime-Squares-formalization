import PrimeSquares.SourceAnnularSymbolFrontier
namespace PrimeSquares
theorem annularConvolution_source_triangle (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hQR : Q ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x‖ ≤
      ‖circleLowOperator (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β (finiteInputLp F f 1) x‖+
      ‖integerMultiplier (sourceCollarDifference N hN Q R q₀ active χ β) (finiteInputLp F f 2) x‖+
      ‖integerMultiplier (sourceLargeHighRemainder N hN Q R q₀ active χ β) (finiteInputLp F f 2) x‖+
      ‖circleMajorArcErrorOperator (sourceRationalCenters R) N hN χ (sourceExceptionalSelector q₀ active) β (finiteInputLp F f 2) x‖ := by
  have h4 (a b c d : ℂ) : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    calc
      _ ≤ ‖a+b+c‖+‖d‖ := norm_add_le _ _
      _ ≤ (‖a+b‖+‖c‖)+‖d‖ := by linarith [norm_add_le (a+b) c]
      _ ≤ _ := by linarith [norm_add_le a b]
  rw [annularConvolution_source_frontier N hN hQ hq₀ hQR active χ β F f x]
  exact h4 _ _ _ _
end PrimeSquares
