import PrimeSquares.OrdinaryCircleLowModel
import PrimeSquares.ExceptionalCircleLowModel
import PrimeSquares.PhysicalLowKernel

namespace PrimeSquares

noncomputable def denominatorCircleLow (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (S : Finset ℕ) : C(PrimeCircle, ℂ) :=
  ordinaryCircleLowModel N Q hN hQ hb-exceptionalCircleLowModel N Q hN hQ hb q₀ χ₀ β S

theorem denominatorCircleLow_kernel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (S : Finset ℕ) (hpos : ∀ d ∈ S,0 < d) (x : ℤ) :
    fourierKernel (denominatorCircleLow N Q hN hQ hb q₀ χ₀ β S) x=physicalLowKernel N Q q₀ χ₀ β S x := by
  rw [denominatorCircleLow,fourierKernel_sub,ordinaryCircleLowModel_kernel,
    exceptionalCircleLowModel_kernel _ _ _ _ _ _ _ _ _ hpos]
  rfl

end PrimeSquares
