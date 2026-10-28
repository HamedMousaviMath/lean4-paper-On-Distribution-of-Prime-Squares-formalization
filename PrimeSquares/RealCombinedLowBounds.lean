import PrimeSquares.RealCombinedLowKernel

open scoped lp
namespace PrimeSquares

theorem realCombinedPhysicalKernel_decay {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (active : Bool) (x : ℤ) :
    ‖realCombinedPhysicalKernel N q₀ χ₀ Q β M active x‖ ≤
      2*realLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 ≤ realLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x :=
    mul_nonneg (realLowAmplitude_nonneg N (by linarith)) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  have he : ‖if active=true then realExceptionalPhysicalKernel N q₀ χ₀ Q β M x else 0‖ ≤
      realLowAmplitude N Q*decayProfile ((N : ℝ)^2) 10 x := by
    by_cases ha : active=true
    · simpa only [ite_eq_left ha] using realExceptionalPhysicalKernel_amplitude hN hQ q₀ χ₀ hχ hβ M x
    · simpa only [ite_eq_right ha,norm_zero] using hn
  calc
    _ ≤ ‖realOrdinaryPhysicalKernel N Q x‖+
        ‖if active=true then realExceptionalPhysicalKernel N q₀ χ₀ Q β M x else 0‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (realOrdinaryPhysicalKernel_amplitude hN hQ x) he
    _ = _ := by ring

theorem realCombinedLowModel_uniform {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (active : Bool) (x : ℤ) :
    ‖fourierKernel (realCombinedLowModel N (by omega) q₀ χ₀ Q (by linarith) hb β M active) x‖ ≤ 2*realLowAmplitude N Q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [realCombinedLowModel_kernel]
  exact (realCombinedPhysicalKernel_decay hN hQ q₀ χ₀ hχ hβ M active x).trans
    (mul_le_of_le_one_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (realLowAmplitude_nonneg N (by linarith)))
      (decayProfile_le_one (sq_pos_of_pos hNp) _ _))

theorem realCombinedLowModel_L1_norm {N : ℕ} (hN : 2 ≤ N) {Q : ℝ} (hQ : 2 ≤ Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (hχ : χ₀.IsQuadratic) {β : ℝ} (hβ : β ≤ 1) (M : ℕ) (active : Bool) :
    ‖fourierL1Operator (realCombinedLowModel N (by omega) q₀ χ₀ Q (by linarith) hb β M active)‖ ≤ 2*realLowAmplitude N Q :=
  fourierL1Operator_opNorm_kernel_bound _ (realCombinedLowModel_uniform hN hQ hb q₀ χ₀ hχ hβ M active)

end PrimeSquares
