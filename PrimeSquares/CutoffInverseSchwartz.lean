import PrimeSquares.SmoothCutoffSchwartz
import PrimeSquares.SchwartzDecayBound
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped FourierTransform
namespace PrimeSquares

noncomputable def sourceCutoffInverse : SchwartzMap ℝ ℂ := 𝓕⁻ sourceCutoffSchwartz

noncomputable def cutoffDecayConstant (K : ℕ) : ℝ :=
  schwartzDecayConstant sourceCutoffInverse K

theorem cutoffDecayConstant_nonneg (K : ℕ) : 0 ≤ cutoffDecayConstant K :=
  schwartzDecayConstant_nonneg _ _

theorem sourceCutoffInverse_fourier (x : ℝ) :
    𝓕 (sourceCutoffInverse : ℝ → ℂ) x = Complex.ofReal (sourceArcCutoff x) := by
  have hf : (𝓕 (𝓕⁻ sourceCutoffSchwartz : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) = sourceCutoffSchwartz :=
    FourierTransform.fourier_fourierInv_eq _
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f x) hf
  simpa only [sourceCutoffInverse,SchwartzMap.fourier_coe,sourceCutoffSchwartz_apply] using h

theorem sourceCutoffInverse_decay (K : ℕ) (x : ℝ) :
    ‖sourceCutoffInverse x‖ ≤ cutoffDecayConstant K/(1+|x|)^K := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1+|x|)^K)).mpr
  simpa only [mul_comm,cutoffDecayConstant] using schwartz_polynomial_decay sourceCutoffInverse K x

end PrimeSquares
