import PrimeSquares.RealExceptionalAmplitude
import PrimeSquares.RealOrdinaryAmplitudeBound

namespace PrimeSquares

noncomputable def realCombinedLowModel (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q : ℝ) (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (M : ℕ) (active : Bool) : C(PrimeCircle, ℂ) :=
  realOrdinaryLowModel N hN Q hQ hb-(if active=true then realExceptionalLowModel N hN q₀ χ₀ Q hQ hb β M else 0)

noncomputable def realCombinedPhysicalKernel (N q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q β : ℝ) (M : ℕ) (active : Bool) (x : ℤ) : ℂ :=
  realOrdinaryPhysicalKernel N Q x-(if active=true then realExceptionalPhysicalKernel N q₀ χ₀ Q β M x else 0)

theorem realCombinedLowModel_kernel (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (M : ℕ) (active : Bool) (x : ℤ) :
    fourierKernel (realCombinedLowModel N hN q₀ χ₀ Q hQ hb β M active) x=
      realCombinedPhysicalKernel N q₀ χ₀ Q β M active x := by
  unfold realCombinedLowModel realCombinedPhysicalKernel
  by_cases ha : active=true
  · simp only [ite_eq_left ha,fourierKernel_sub,realOrdinaryLowModel_kernel,realExceptionalLowModel_kernel]
  · simp only [ite_eq_right ha,sub_zero,realOrdinaryLowModel_kernel]

end PrimeSquares
