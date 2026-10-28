import PrimeSquares.PhysicalLowL1Operator

open Finset
namespace PrimeSquares

theorem physicalLow_indicator_bound {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (physicalLowKernel N Q q₀ χ₀ β S) F x‖ ≤ physicalLowAmplitude N Q*(F.card : ℝ) := by
  obtain ⟨T,hT,_,hi⟩ := physicalLow_L1_operator hN hQ q₀ χ₀ hχ hβ S hS hwidth
  rw [←hi]
  have hb := (T.le_opNorm (finiteIndicatorLp F 1)).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  rw [finiteIndicatorLp_one_norm] at hb
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (T (finiteIndicatorLp F 1)) x).trans hb

theorem physicalLow_pairing_bound {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (F G : Finset ℤ) :
    ‖restrictedKernelPairing (physicalLowKernel N Q q₀ χ₀ β S) F G‖ ≤
      physicalLowAmplitude N Q*(F.card : ℝ)*(G.card : ℝ) := by
  calc
    _ ≤ ∑ x ∈ G,‖indicatorConvolution (physicalLowKernel N Q q₀ χ₀ β S) F x‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G,physicalLowAmplitude N Q*(F.card : ℝ) :=
      sum_le_sum (fun x _ => physicalLow_indicator_bound hN hQ q₀ χ₀ hχ hβ S hS hwidth F x)
    _ = _ := by simp [mul_comm]

end PrimeSquares
