import PrimeSquares.RealFourierDilation
import PrimeSquares.ScaledCutoffKernel

open scoped FourierTransform
namespace PrimeSquares

theorem scaledCutoffKernel_inverse_transform {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕⁻ (fun ξ : ℝ => Complex.ofReal (sourceArcCutoff (a*ξ))) x=scaledCutoffKernel a x := by
  rw [real_inverse_fourier_dilate (fun ξ : ℝ => Complex.ofReal (sourceArcCutoff ξ)) ha]
  change Complex.ofReal a⁻¹*𝓕⁻ (sourceCutoffSchwartz : ℝ → ℂ) (x/a)=_
  rw [←SchwartzMap.fourierInv_coe]
  rfl

theorem scaledCutoffInverse_decay {a : ℝ} (ha : 0 < a) (K : ℕ) (x : ℝ) :
    ‖𝓕⁻ (fun ξ : ℝ => Complex.ofReal (sourceArcCutoff (a*ξ))) x‖ ≤
      cutoffDecayConstant K/a*decayProfile a K x := by
  rw [scaledCutoffKernel_inverse_transform ha]
  exact scaledCutoffKernel_decay ha K x

end PrimeSquares
