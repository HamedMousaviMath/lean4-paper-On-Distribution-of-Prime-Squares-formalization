import PrimeSquares.RealOrdinaryL1Bound
import PrimeSquares.AllInputFourierConvolution
import PrimeSquares.UniformL1Maximum

open scoped lp
namespace PrimeSquares

theorem realOrdinaryLow_countable_maximal {N₀ : ℕ} (hN₀ : 2 ≤ N₀) {Q : ℝ} (hQ : 2 ≤ Q)
    (N : ℕ → ℕ) (hN : ∀ j,N₀ ≤ N j) (hb : ∀ j,2*Q ≤ (N j : ℝ)^2) (f : ℓ¹(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖integerMultiplier
        (realOrdinaryLowModel (N j) (by have h := hN j;omega) Q (by linarith) (hb j))
        (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖) ∧
      ‖g‖ ≤ realLowAmplitude N₀ Q*‖f‖ := by
  let m (j : ℕ) := realOrdinaryLowModel (N j) (by have h := hN j;omega) Q (by linarith) (hb j)
  let T (j : ℕ) := fourierL1Operator (m j)
  have hT : ∀ j,‖T j‖ ≤ realLowAmplitude N₀ Q := fun j =>
    (realOrdinaryLowModel_L1_norm (by have h := hN j;omega) hQ (hb j)).trans
      (realLowAmplitude_scale_mono (by omega) (hN j) (by linarith))
  refine ⟨operatorL1Maximum T hT f,?_,operatorL1Maximum_norm T hT f⟩
  intro x
  change (⨆ j : ℕ,‖fourierL1Operator (m j) f x‖)=_
  exact iSup_congr (fun j => congrArg norm (fourierL1Operator_all_l2_agreement (m j) f x))

end PrimeSquares
