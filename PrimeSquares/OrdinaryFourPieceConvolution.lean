import PrimeSquares.OrdinaryFourPieceOperator
import PrimeSquares.CircleFiniteDecomposition

open scoped lp
namespace PrimeSquares

theorem annularConvolution_ordinary_four_piece (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q R B : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hB : 0 < B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x=
      circleLowOperator (sourceRationalCenters R) N hN q₀ Q B χ (fun _ => 0) β (finiteInputLp F f 1) x+
      integerMultiplier (rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss)
        (finiteInputLp F f 2) x+
      circleMajorArcOperator ((sourceRationalCenters R).filter (fun r => Q < (r.den : ℝ))) N hN χ (fun _ => 0) β
        (finiteInputLp F f 2) x+
      circleMajorArcErrorOperator (sourceRationalCenters R) N hN χ (fun _ => 0) β (finiteInputLp F f 2) x := by
  have hh := annularKernel_finite_low_high_error (sourceRationalCenters R) N hN q₀ Q B χ (fun _ => 0) β F f x
  rw [circleHighOperator,circleHighModel_ordinary_full_split N hN q₀ hq₀ hQ hQR hB χ β,integerMultiplier_add] at hh
  simpa only [_root_.add_apply,lp.coeFn_add,Pi.add_apply,add_assoc,circleMajorArcOperator] using hh

end PrimeSquares
