import PrimeSquares.PhysicalLowAmplitude
import PrimeSquares.FiniteDecayTail

namespace PrimeSquares

theorem physicalLow_far_field {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) {R : ℝ} (hR : 0 ≤ R)
    (hF : ∀ y ∈ F,R ≤ |((x-y : ℤ) : ℝ)|) :
    ‖finiteConvolution (physicalLowKernel N Q q₀ χ₀ β S) F f x‖ ≤
      physicalLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 R*∑ y ∈ F,‖f y‖ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact finiteConvolution_outside_ball _ (physicalLowAmplitude_nonneg N Q (by omega)) (sq_pos_of_pos hNp) hR 10
    (physicalLowKernel_decay hN hQ q₀ χ₀ hχ hβ S hS hwidth) F f x hF

end PrimeSquares
