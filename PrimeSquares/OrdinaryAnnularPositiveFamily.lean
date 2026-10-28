import PrimeSquares.ActualPositiveSquareFamilies
import PrimeSquares.DyadicSquareReconstruction

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def ordinaryAnnularDyadicFamily : PositiveAverageFamily where
  indices j := Ioc (((2 : ℕ)^j)/2) ((2 : ℕ)^j)
  shift n := (n : ℤ)^2
  weight j n := (((2 : ℕ)^j : ℕ) : ℝ)⁻¹*(fun _ => 1) n
  mass := 1
  mass_one_le := le_rfl
  nonnegative _ _ _ := by positivity
  mass_bound j := by
    rw [←mul_sum]
    exact normalized_square_mass_le (by positivity : (0 : ℕ) < 2^j)
      _ (annularIndices_subset ((2 : ℕ)^j)) _ (fun _ => by norm_num)
      (by simp)

theorem ordinaryAnnularDyadicFamily_apply (j : ℕ) (f : ℓ²(ℤ,ℂ)) (x : ℤ) :
    positiveAverage ordinaryAnnularDyadicFamily j (f : ℤ → ℂ) x =
      annularWeightedSquareAverage (P := 2) (by norm_num) ((2 : ℕ)^j) (fun _ => 1) f x := by
  unfold positiveAverage
  rw [annularWeightedSquareAverage_apply, mul_sum]
  change (∑ n ∈ Ioc (((2 : ℕ)^j)/2) ((2 : ℕ)^j),
    Complex.ofReal ((((2 : ℕ)^j : ℕ) : ℝ)⁻¹*(fun _ => 1) n)*f (x-(n : ℤ)^2)) = _
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem ordinaryAnnularDyadicFamily_mass :
    ordinaryAnnularDyadicFamily.mass = 1 := rfl

end PrimeSquares
