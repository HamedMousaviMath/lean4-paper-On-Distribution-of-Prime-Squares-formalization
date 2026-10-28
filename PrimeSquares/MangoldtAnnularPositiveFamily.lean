import PrimeSquares.ActualPositiveSquareFamilies
import PrimeSquares.DyadicSquareReconstruction

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def mangoldtAnnularDyadicFamily : PositiveAverageFamily where
  indices j := Ioc (((2 : ℕ)^j)/2) ((2 : ℕ)^j)
  shift n := (n : ℤ)^2
  weight j n := (((2 : ℕ)^j : ℕ) : ℝ)⁻¹*ArithmeticFunction.vonMangoldt n
  mass := primeSquareChebyshevConstant
  mass_one_le := mangoldtPositiveFamily.mass_one_le
  nonnegative _ _ _ := mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg
  mass_bound j := by
    rw [←mul_sum]
    exact normalized_square_mass_le (by positivity : (0 : ℕ) < 2^j)
      _ (annularIndices_subset ((2 : ℕ)^j)) _ (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
      (mangoldt_square_mass_bound ((2 : ℕ)^j))

theorem mangoldtAnnularDyadicFamily_apply (j : ℕ) (f : ℓ²(ℤ,ℂ)) (x : ℤ) :
    positiveAverage mangoldtAnnularDyadicFamily j (f : ℤ → ℂ) x =
      annularWeightedSquareAverage (P := 2) (by norm_num) ((2 : ℕ)^j) ArithmeticFunction.vonMangoldt f x := by
  unfold positiveAverage
  rw [annularWeightedSquareAverage_apply, mul_sum]
  change (∑ n ∈ Ioc (((2 : ℕ)^j)/2) ((2 : ℕ)^j),
    Complex.ofReal ((((2 : ℕ)^j : ℕ) : ℝ)⁻¹*ArithmeticFunction.vonMangoldt n)*f (x-(n : ℤ)^2)) = _
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem mangoldtAnnularDyadicFamily_mass :
    mangoldtAnnularDyadicFamily.mass = primeSquareChebyshevConstant := rfl

end PrimeSquares
