import PrimeSquares.GoldbachUpperSieveDensity
import PrimeSquares.GoldbachWeightedUpperMainTerm
import PrimeSquares.GoldbachSieveNumericalComparison

set_option autoImplicit false
namespace PrimeSquares

/-- Only independent classical general theorems and their normalizations.
No manuscript sequence, sieve conclusion or Goldbach endpoint is a field. -/
structure GoldbachSection11Inputs where
  siegelWalfisz : RawPrimeSiegelWalfiszInput
  bombieriVinogradov : RawPrimeBombieriVinogradovInput
  minorArcs : UniformRenGhoshInputs
  K : ℝ
  K₀ : ℝ
  c : ℝ
  sstar : ℝ
  K₁ : ℝ
  δ : ℝ
  K_nonneg : 0≤K
  K₀_nonneg : 0≤K₀
  c_pos : 0<c
  δ_pos : 0<δ
  intervalHalf : GoldbachClassicalIntervalMertens K
  intervalFull : GoldbachClassicalFullIntervalMertens K
  primeLogs : ClassicalPrimeLogMertens K
  primeRatios : ClassicalPrimeMertensRatios K
  halfMean : ClassicalHalfMeanValueInput
  fundamental : GoldbachClassicalFundamentalInput 2 K K₀ c sstar
  fHalf : ℝ→ℝ
  FHalf : ℝ→ℝ
  fOne : ℝ→ℝ
  FOne : ℝ→ℝ
  coefficientHalf : GoldbachClassicalCoefficientInput (1/2) K K₁ δ fHalf FHalf
  coefficientOne : GoldbachClassicalCoefficientInput 1 K K₁ δ fOne FOne
  halfContinuous : ContinuousAt fHalf (9/8)
  oneContinuous : ContinuousAt FOne 2
  halfValue : fHalf (9/8)=goldbachSieveLowerValue
  oneValue : FOne 2=Real.exp Real.eulerMascheroniConstant

theorem goldbach_section11_sieve_gap_positive (H : GoldbachSection11Inputs) :
    0<H.fHalf (9/8)-goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8) := by
  exact goldbach_normalized_sieve_comparison H.fHalf H.FOne H.halfValue H.oneValue

end PrimeSquares
