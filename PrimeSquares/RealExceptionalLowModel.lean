import PrimeSquares.RealExceptionalTermKernel

open Finset
namespace PrimeSquares

noncomputable def realExceptionalLowModel (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q : ℝ) (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (M : ℕ) : C(PrimeCircle, ℂ) :=
  ∑ d ∈ realExceptionalDenominators q₀ M Q,realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β (q₀*d)

noncomputable def realExceptionalPhysicalKernel (N q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q β : ℝ) (M : ℕ) (x : ℤ) : ℂ :=
  ∑ d ∈ realExceptionalDenominators q₀ M Q,inducedIntegerCorrelation q₀ χ₀ d x*
    smoothedAnnularKernel N β (exceptionalLowWidth N Q (conductorMajorant q₀) d) x

theorem realExceptionalLowModel_kernel (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (M : ℕ) (x : ℤ) :
    fourierKernel (realExceptionalLowModel N hN q₀ χ₀ Q hQ hb β M) x=realExceptionalPhysicalKernel N q₀ χ₀ Q β M x := by
  rw [realExceptionalLowModel,fourierKernel_sum,realExceptionalPhysicalKernel]
  apply sum_congr rfl
  intro d hd
  have : NeZero d := ⟨by have h := (mem_realExceptionalDenominators (NeZero.pos q₀) Q).mp hd;omega⟩
  exact realExceptionalCircleTerm_kernel N hN q₀ d χ₀ hQ hb β x

end PrimeSquares
