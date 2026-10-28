import PrimeSquares.PhysicalLowL1Operator
import PrimeSquares.UniformL1Maximum

open scoped lp
namespace PrimeSquares

theorem physicalLow_kernel_uniform_tail {N₀ N Q : ℕ} (hN₀ : 2 ≤ N₀) (hN : N₀ ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (x : ℤ) :
    ‖physicalLowKernel N Q q₀ χ₀ β S x‖ ≤ physicalLowAmplitude N₀ Q :=
  (physicalLowKernel_uniform (hN₀.trans hN) hQ q₀ χ₀ hχ hβ S hS hwidth x).trans
    (physicalLowAmplitude_mono (by omega) hN (by omega))

theorem physicalLow_countable_L1_maximum {N₀ Q : ℕ} (hN₀ : 2 ≤ N₀) (hQ : 2 ≤ Q)
    (N q₀ : ℕ → ℕ) (hq₀ : ∀ j,0 < q₀ j) (χ₀ : ∀ j,DirichletCharacter ℂ (q₀ j))
    (hN : ∀ j,N₀ ≤ N j) (hχ : ∀ j,(χ₀ j).IsQuadratic) (β : ℕ → ℝ)
    (hβ : ∀ j,β j ≤ 1) (S : ℕ → Finset ℕ) (hS : ∀ j,S j ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ j,∀ d ∈ S j,conductorMajorant (q₀ j)*(d : ℝ) ≤ Q)
    (f : ℓ¹(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖∑' y : ℤ,
        (by have : NeZero (q₀ j) := ⟨(hq₀ j).ne'⟩;exact physicalLowKernel (N j) Q (q₀ j) (χ₀ j) (β j) (S j) (x-y))*f y‖) ∧
      ‖g‖ ≤ physicalLowAmplitude N₀ Q*‖f‖ := by
  have (j : ℕ) : NeZero (q₀ j) := ⟨(hq₀ j).ne'⟩
  let hK (j : ℕ) := physicalLow_kernel_uniform_tail hN₀ (hN j) hQ (q₀ j) (χ₀ j) (hχ j) (hβ j) (S j) (hS j) (hwidth j)
  let T (j : ℕ) := kernelL1Operator (physicalLowKernel (N j) Q (q₀ j) (χ₀ j) (β j) (S j)) (hK j)
  have hT : ∀ j,‖T j‖ ≤ physicalLowAmplitude N₀ Q := fun j => kernelL1Operator_norm _ (hK j)
  refine ⟨operatorL1Maximum T hT f,?_,operatorL1Maximum_norm T hT f⟩
  intro x
  rfl

end PrimeSquares
