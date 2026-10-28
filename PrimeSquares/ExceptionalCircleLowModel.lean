import PrimeSquares.ExceptionalCircleLowTerm
import PrimeSquares.ExceptionalPhysicalLow

open Finset
namespace PrimeSquares

noncomputable def exceptionalCircleLowModel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (S : Finset ℕ) : C(PrimeCircle, ℂ) :=
  ∑ d ∈ S,exceptionalCircleLowTerm N Q hN hQ hb q₀ χ₀ β d

theorem exceptionalCircleLowModel_kernel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (S : Finset ℕ) (hpos : ∀ d ∈ S,0 < d) (x : ℤ) :
    fourierKernel (exceptionalCircleLowModel N Q hN hQ hb q₀ χ₀ β S) x=exceptionalPhysicalLowKernel N Q q₀ χ₀ β S x := by
  rw [exceptionalCircleLowModel,fourierKernel_sum,exceptionalPhysicalLowKernel]
  apply sum_congr rfl
  intro d hd
  have : NeZero d := ⟨(hpos d hd).ne'⟩
  exact exceptionalCircleLowTerm_kernel N Q hN hQ hb q₀ d χ₀ β x

end PrimeSquares
