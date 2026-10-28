import PrimeSquares.CircleHighLowKernels
import PrimeSquares.FourierL1Operator

open scoped lp
namespace PrimeSquares

noncomputable def circleLowOperator (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤ :=
  fourierL1Operator (circleLowModel Γ N hN q₀ Q B₀ χ κ β)

noncomputable def circleHighOperator (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  integerMultiplier (circleHighModel Γ N hN q₀ Q B₀ χ κ β)

theorem circleLowOperator_finite (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    circleLowOperator Γ N hN q₀ Q B₀ χ κ β (finiteInputLp F f 1) x =
      finiteConvolution (circleLowKernel Γ N hN q₀ Q B₀ χ κ β) F f x :=
  kernelL1Operator_finite _ _ F f x

theorem circleHighOperator_finite (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    circleHighOperator Γ N hN q₀ Q B₀ χ κ β (finiteInputLp F f 2) x =
      finiteConvolution (circleHighKernel Γ N hN q₀ Q B₀ χ κ β) F f x :=
  integerMultiplier_finite_convolution _ F f x

end PrimeSquares
