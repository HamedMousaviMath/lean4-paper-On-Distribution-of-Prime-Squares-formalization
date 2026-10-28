import PrimeSquares.CutoffInverseSchwartz
import PrimeSquares.DecayProfile

namespace PrimeSquares

noncomputable def scaledCutoffKernel (a x : ℝ) : ℂ :=
  Complex.ofReal a⁻¹*sourceCutoffInverse (x/a)

theorem scaledCutoffKernel_continuous (a : ℝ) : Continuous (scaledCutoffKernel a) := by
  unfold scaledCutoffKernel
  exact continuous_const.mul (sourceCutoffInverse.continuous.comp (continuous_id.div_const a))

theorem scaledCutoffKernel_decay {a : ℝ} (ha : 0 < a) (K : ℕ) (x : ℝ) :
    ‖scaledCutoffKernel a x‖ ≤ cutoffDecayConstant K/a*decayProfile a K x := by
  rw [scaledCutoffKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr ha.le)]
  have h := mul_le_mul_of_nonneg_left (sourceCutoffInverse_decay K (x/a)) (inv_nonneg.mpr ha.le)
  simpa only [abs_div,abs_mul,abs_inv,abs_of_pos ha,decayProfile,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

theorem scaledCutoffKernel_uniform {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖scaledCutoffKernel a x‖ ≤ cutoffDecayConstant 0/a := by
  simpa [decayProfile] using scaledCutoffKernel_decay ha 0 x

end PrimeSquares
