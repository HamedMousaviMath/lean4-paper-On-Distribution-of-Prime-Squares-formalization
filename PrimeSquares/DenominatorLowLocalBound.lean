import PrimeSquares.DenominatorLowKernelDecay
import PrimeSquares.PhysicalLowLocalBound

namespace PrimeSquares

theorem denominatorCircleLow_finite_convolution {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (β : ℝ) (S : Finset ℕ) (hpos : ∀ d ∈ S,0 < d)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    integerMultiplier (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S) (finiteInputLp F f 2) x=
      finiteConvolution (physicalLowKernel N Q q₀ χ₀ β S) F f x := by
  rw [integerMultiplier_finite_convolution]
  unfold finiteConvolution
  apply Finset.sum_congr rfl
  intro y _
  rw [denominatorCircleLow_kernel _ _ _ _ _ _ _ _ _ hpos]

theorem denominatorCircleLow_local_finite {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖integerMultiplier (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S) (finiteInputLp F f 2) x‖ ≤
      (4*lowSpatialConstant*(Q : ℝ)*Real.log (2*(Q : ℝ)))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  rw [denominatorCircleLow_finite_convolution hN hQ hb q₀ χ₀ β S (fun d hd => (Finset.mem_Icc.mp (hS hd)).1)]
  exact physicalLowKernel_local_finite hN hQ q₀ χ₀ hχ hβ S hS hw F f x

end PrimeSquares
