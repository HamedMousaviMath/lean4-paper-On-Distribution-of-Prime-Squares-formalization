import PrimeSquares.QuadraticWeylArcBounds
import PrimeSquares.DyadicSquareReconstruction

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem annularSquareSymbol_two_mul_value (M : ℕ) (w : ℕ → ℝ) (ξ : PrimeCircle) :
    annularWeightedSquareAverageSymbol (2*M) w ξ =
      weightedSquareAverageSymbol (2*M) w ξ-(1/2 : ℂ)*weightedSquareAverageSymbol M w ξ := by
  simp only [annularWeightedSquareAverageSymbol, weightedSquareAverageSymbol, finiteSquareSymbol_apply]
  rw [show (2*M)/2 = M by omega]
  have hsum := sum_Ioc_consecutive (fun n : ℕ => (w n : ℂ)*negativeFourierCharacter ((n : ℤ)^2) ξ)
    (Nat.zero_le M) (show M ≤ 2*M by omega)
  rw [←hsum, ←mul_assoc, square_half_normalization]
  ring

theorem initialQuadraticModel_annular_two_mul {M : ℕ} (hM : 1 ≤ M) (θ : ℝ) :
    annularOscillatoryModel (2*M) 1 θ = initialQuadraticModel (2*M) θ-(1/2 : ℂ)*initialQuadraticModel M θ := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (quadraticOscillation_intervalIntegrable θ 0 M) (quadraticOscillation_intervalIntegrable θ M (2*M))
  rw [annularOscillatoryModel_interval]
  simp only [sub_self, Real.rpow_zero, Complex.ofReal_one, one_mul]
  rw [show ((2*M : ℕ) : ℝ)/2 = (M : ℝ) by push_cast; ring]
  unfold initialQuadraticModel
  rw [show (((2*M : ℕ) : ℝ)) = 2*(M : ℝ) by push_cast; ring]
  rw [←hi]
  have he : Complex.ofReal ((2*(M : ℝ))⁻¹) = (1/2 : ℂ)*Complex.ofReal ((M : ℝ)⁻¹) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (square_half_normalization M).symm
  rw [he]
  ring

theorem quadratic_weyl_annular_major {E R ξ : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) {M : ℕ} (hM : 1 ≤ M)
    (hR : 0 ≤ R) (hNR : 32*R ≤ ((2*M : ℕ) : ℝ)) {s : ℚ} (hs : (s.den : ℝ) ≤ R)
    (harc : |ξ-(s : ℝ)| ≤ R/((s.den : ℝ)*((2*M : ℕ) : ℝ)^2)) :
    ‖annularWeightedSquareAverageSymbol (2*M) (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss s*annularOscillatoryModel (2*M) 1 (ξ-(s : ℝ))‖ ≤
        4*E*Real.sqrt R/((2*M : ℕ) : ℝ) := by
  have hN : 1 ≤ 2*M := by omega
  have hfirst := quadratic_weyl_major_approximation hE HE hN hN hR
    (by have h := (Nat.cast_nonneg (2*M) : (0 : ℝ) ≤ ((2*M : ℕ) : ℝ)); linarith) (by omega) hNR hs harc
  have hsecond := quadratic_weyl_major_approximation hE HE hN hM hR
    (by push_cast; linarith) (by omega) hNR hs harc
  rw [annularSquareSymbol_two_mul_value, initialQuadraticModel_annular_two_mul hM]
  have he : weightedSquareAverageSymbol (2*M) (fun _ => 1) (ξ : PrimeCircle)-
      (1/2 : ℂ)*weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss s*(initialQuadraticModel (2*M) (ξ-(s : ℝ))-
        (1/2 : ℂ)*initialQuadraticModel M (ξ-(s : ℝ))) =
      (weightedSquareAverageSymbol (2*M) (fun _ => 1) (ξ : PrimeCircle)-
        rationalFullSquareGauss s*initialQuadraticModel (2*M) (ξ-(s : ℝ)))-
      (1/2 : ℂ)*(weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
        rationalFullSquareGauss s*initialQuadraticModel M (ξ-(s : ℝ))) := by ring
  rw [he]
  have hsecond' : ‖(1/2 : ℂ)*(weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss s*initialQuadraticModel M (ξ-(s : ℝ)))‖ ≤
      (1/2 : ℝ)*(2*E*Real.sqrt R/((2*M : ℕ) : ℝ)) := by
    rw [norm_mul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left hsecond (by norm_num)
  have hnorm := (norm_sub_le _ _).trans (add_le_add hfirst hsecond')
  have hpos : 0 ≤ E*Real.sqrt R/((2*M : ℕ) : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hnorm hpos ⊢
  nlinarith

theorem quadratic_weyl_annular_outside {E R ξ : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) {M : ℕ} (hM : 1 ≤ M) (hR : 0 < R)
    (hout : OutsideSourceMajorArcs (2*M) R ξ) :
    ‖annularWeightedSquareAverageSymbol (2*M) (fun _ => 1) (ξ : PrimeCircle)‖ ≤
      6*quadraticIntegralConstant/Real.sqrt R+12*E/Real.sqrt ((2*M : ℕ) : ℝ) := by
  have hN : 1 ≤ 2*M := by omega
  have hfirst := quadratic_weyl_initial_outside hE HE hN hN hR
    (by have h := (Nat.cast_nonneg (2*M) : (0 : ℝ) ≤ ((2*M : ℕ) : ℝ)); linarith) hout
  have hsecond := quadratic_weyl_initial_outside hE HE hN hM hR (by push_cast; linarith) hout
  rw [annularSquareSymbol_two_mul_value]
  have hsecond' : ‖(1/2 : ℂ)*weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)‖ ≤
      (1/2 : ℝ)*(4*quadraticIntegralConstant/Real.sqrt R+8*E/Real.sqrt ((2*M : ℕ) : ℝ)) := by
    rw [norm_mul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left hsecond (by norm_num)
  have h := (norm_sub_le _ _).trans (add_le_add hfirst hsecond')
  convert h using 1
  ring

end PrimeSquares
