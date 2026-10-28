import PrimeSquares.PhysicalLowAmplitude
import PrimeSquares.DecayL1Convolution
import PrimeSquares.KernelL1FiniteAgreement

open scoped lp
namespace PrimeSquares

theorem physicalLowKernel_uniform {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) :
    ∀ x : ℤ,‖physicalLowKernel N Q q₀ χ₀ β S x‖ ≤ physicalLowAmplitude N Q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact decay_kernel_uniform _ (physicalLowAmplitude_nonneg N Q (by omega)) (sq_pos_of_pos hNp) 10
    (physicalLowKernel_decay hN hQ q₀ χ₀ hχ hβ S hS hwidth)

theorem physicalLow_L1_operator {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) :
    ∃ T : ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤,
      ‖T‖ ≤ physicalLowAmplitude N Q ∧
      (∀ f : ℓ¹(ℤ, ℂ),∀ x : ℤ,T f x=∑' y : ℤ,physicalLowKernel N Q q₀ χ₀ β S (x-y)*f y) ∧
      (∀ F : Finset ℤ,∀ x : ℤ,T (finiteIndicatorLp F 1) x=indicatorConvolution (physicalLowKernel N Q q₀ χ₀ β S) F x) := by
  let hK := physicalLowKernel_uniform hN hQ q₀ χ₀ hχ hβ S hS hwidth
  exact ⟨kernelL1Operator _ hK,kernelL1Operator_norm _ hK,
    kernelL1Operator_apply _ hK,kernelL1Operator_indicator _ hK⟩

end PrimeSquares
