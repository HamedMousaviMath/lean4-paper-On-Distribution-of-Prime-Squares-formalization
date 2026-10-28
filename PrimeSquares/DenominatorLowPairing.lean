import PrimeSquares.DenominatorLowL1Bound
import PrimeSquares.AllInputFourierConvolution
import PrimeSquares.PhysicalLowPairing

open scoped lp
namespace PrimeSquares

theorem denominatorCircleLow_all_l2_low_bound {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    ‖integerMultiplier (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S)
      (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖ ≤ physicalLowAmplitude N Q*‖f‖ := by
  rw [←fourierL1Operator_all_l2_agreement]
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x).trans
    (denominatorCircleLow_L1_bound hN hQ hb q₀ χ₀ hχ hβ S hS hw f)

theorem denominatorCircleLow_pairing {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hw : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (F G : Finset ℤ) :
    ‖restrictedKernelPairing (fourierKernel (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S)) F G‖ ≤
      physicalLowAmplitude N Q*(F.card : ℝ)*(G.card : ℝ) := by
  have he : fourierKernel (denominatorCircleLow N Q (by omega) (by omega) hb q₀ χ₀ β S)=physicalLowKernel N Q q₀ χ₀ β S :=
    funext (denominatorCircleLow_kernel _ _ _ _ _ _ _ _ _ (fun d hd => (Finset.mem_Icc.mp (hS hd)).1))
  rw [he]
  exact physicalLow_pairing_bound hN hQ q₀ χ₀ hχ hβ S hS hw F G

end PrimeSquares
