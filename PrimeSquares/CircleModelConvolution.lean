import PrimeSquares.CircleModelKernels
import PrimeSquares.CircleModelOperators

open scoped lp
namespace PrimeSquares

theorem circleModelOperator_finite_convolution (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    circleMajorArcOperator Γ N hN χ κ β (finiteInputLp F f 2) x =
      finiteConvolution (circleModelKernel Γ N hN χ κ β) F f x :=
  integerMultiplier_finite_convolution _ F f x

theorem circleModelErrorOperator_finite_convolution (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    circleMajorArcErrorOperator Γ N hN χ κ β (finiteInputLp F f 2) x =
      finiteConvolution (circleModelErrorKernel Γ N hN χ κ β) F f x :=
  integerMultiplier_finite_convolution _ F f x

end PrimeSquares
