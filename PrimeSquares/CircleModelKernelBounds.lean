import PrimeSquares.CircleModelKernels
import PrimeSquares.UniformFourierKernel

open Finset
namespace PrimeSquares

theorem circleModelKernel_bound {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : ∀ r ∈ Γ, ‖κ r‖ ≤ 1) (x : ℤ) :
    ‖circleModelKernel Γ N (by omega) χ κ β x‖ ≤
      ∑ r ∈ Γ, 3*(gaussModelConstant*(r.den : ℝ)^(-(5/12 : ℝ))) :=
  fourierKernel_uniform_bound _ (circleMajorArcModel_norm hN Γ χ κ hβ0 hβ1 hκ) x

theorem circleModelErrorKernel_bound (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ)
    {B : ℝ} (he : ∀ θ, ‖circleMajorArcError Γ N hN χ κ β θ‖ ≤ B) (x : ℤ) :
    ‖circleModelErrorKernel Γ N hN χ κ β x‖ ≤ B :=
  fourierKernel_uniform_bound _ he x

end PrimeSquares
