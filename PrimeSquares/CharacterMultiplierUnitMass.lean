import PrimeSquares.AnnularSourceFinitePairing
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem characterMultiplier_unit_mass (j : ℤ) :
    integerMultiplier (negativeFourierCharacter j) (lp.single 2 (0 : ℤ) (1 : ℂ))=
      lp.single 2 j (1 : ℂ) := by
  apply integerFourier.injective
  rw [integerFourier_multiplier,integerFourier_single,integerFourier_single]
  simp only [neg_zero,one_smul]
  apply Lp.ext
  filter_upwards [circleMultiply_ae (negativeFourierCharacter j) (fourierLp (T := (1 : ℝ)) 2 0),
    coeFn_fourierLp (T := (1 : ℝ)) 2 0,coeFn_fourierLp (T := (1 : ℝ)) 2 (-j)] with θ hm h0 hj
  rw [hm,h0,hj]
  simp only [negativeFourierCharacter,fourier_zero,mul_one]
end PrimeSquares
