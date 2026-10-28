import PrimeSquares.PhysicalLowAmplitude
import PrimeSquares.FiniteLocalConvolution

namespace PrimeSquares

theorem physicalLowKernel_local_finite {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution (physicalLowKernel N Q q₀ χ₀ β S) F f x‖ ≤
      (4*lowSpatialConstant*(Q : ℝ)*Real.log (2*(Q : ℝ)))*
        dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hA : 0 ≤ lowSpatialConstant*(Q : ℝ)*Real.log (2*(Q : ℝ)) :=
    mul_nonneg (mul_nonneg lowSpatialConstant_nonneg (Nat.cast_nonneg _)) (Real.log_nonneg (by linarith))
  have h := finiteConvolution_local_mass (physicalLowKernel N Q q₀ χ₀ β S) hA
    (sq_pos_of_pos hNp) (physicalLowKernel_decay hN hQ q₀ χ₀ hχ hβ S hS hwidth) F f x
  convert h using 1; ring

end PrimeSquares
