import PrimeSquares.DenominatorCircleLow
import PrimeSquares.PhysicalLowL1Operator

namespace PrimeSquares

theorem denominatorCircleLow_kernel_decay {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (x : ℤ) :
    ‖fourierKernel (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S) x‖ ≤
      physicalLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x := by
  rw [denominatorCircleLow_kernel _ _ _ _ _ _ _ _ _ (fun d hd => (Finset.mem_Icc.mp (hS hd)).1)]
  exact physicalLowKernel_decay hN hQ q₀ χ₀ hχ hβ S hS hw x

theorem denominatorCircleLow_kernel_uniform {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (x : ℤ) :
    ‖fourierKernel (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S) x‖ ≤ physicalLowAmplitude N Q := by
  rw [denominatorCircleLow_kernel _ _ _ _ _ _ _ _ _ (fun d hd => (Finset.mem_Icc.mp (hS hd)).1)]
  exact physicalLowKernel_uniform hN hQ q₀ χ₀ hχ hβ S hS hw x

end PrimeSquares
