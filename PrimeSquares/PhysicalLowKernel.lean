import PrimeSquares.OrdinaryPhysicalLow
import PrimeSquares.ExceptionalPhysicalLow

namespace PrimeSquares

noncomputable def physicalLowKernel (N Q q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (S : Finset ℕ) (x : ℤ) : ℂ :=
  ordinaryPhysicalLowKernel N Q x-exceptionalPhysicalLowKernel N Q q₀ χ₀ β S x

noncomputable def lowSpatialConstant : ℝ :=
  512*cutoffDecayConstant 10*(cohenLogConstant/2+correlationLogConstant)

theorem lowSpatialConstant_nonneg : 0 ≤ lowSpatialConstant := by
  unfold lowSpatialConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (cutoffDecayConstant_nonneg _))
    (add_nonneg (div_nonneg cohenLogConstant_pos.le (by norm_num : (0 : ℝ) ≤ 2)) correlationLogConstant_pos.le)

theorem physicalLowKernel_decay {N Q : ℕ} (hN : 2 ≤ N) (hQ : 2 ≤ Q)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    {β : ℝ} (hβ : β ≤ 1) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hwidth : ∀ d ∈ S,conductorMajorant q₀*(d : ℝ) ≤ Q) (x : ℤ) :
    ‖physicalLowKernel N Q q₀ χ₀ β S x‖ ≤
      (lowSpatialConstant*(Q : ℝ)*Real.log (2*(Q : ℝ))/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x := by
  have hC := cutoffDecayConstant_nonneg 10
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : Real.log ((Q : ℝ)+1) ≤ Real.log (2*(Q : ℝ)) := Real.log_le_log (by positivity) (by linarith)
  have hc : 0 ≤ 512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2*decayProfile ((N : ℝ)^2) 10 x :=
    mul_nonneg (by positivity) (decayProfile_pos (sq_pos_of_pos hNp) _ _).le
  calc
    _ ≤ ‖ordinaryPhysicalLowKernel N Q x‖+‖exceptionalPhysicalLowKernel N Q q₀ χ₀ β S x‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (ordinaryPhysicalLowKernel_decay hN hQ x)
      (exceptionalPhysicalLowKernel_decay hN (by omega) q₀ χ₀ hχ hβ S hS hwidth x)
    _ ≤ (512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x*
        ((cohenLogConstant/2)*Real.log (2*(Q : ℝ)))+
      (512*cutoffDecayConstant 10*(Q : ℝ)/(N : ℝ)^2)*decayProfile ((N : ℝ)^2) 10 x*
        (correlationLogConstant*Real.log (2*(Q : ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlog (div_nonneg cohenLogConstant_pos.le (by norm_num : (0 : ℝ) ≤ 2))) hc) le_rfl
    _ = _ := by unfold lowSpatialConstant;ring

end PrimeSquares
