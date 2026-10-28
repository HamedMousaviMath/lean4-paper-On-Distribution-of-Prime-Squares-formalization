import PrimeSquares.ScaledCutoffL1
import PrimeSquares.RealMultiplierComposition

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

/-- Independent Young L1 convolution theorem in its Fourier-multiplier
form, for arbitrary integrable complex kernels and their exact symbols.
The general L2/Fourier identification is included in this standard theorem
boundary. No cutoff, annular, IW or maximal conclusion is a field. -/
def RawYoungMultiplierInput : Prop :=
  ∀ K : ℝ→ℂ,Integrable K volume →
    ∀ m : BoundedContinuousFunction ℝ ℂ,(∀ θ,𝓕 K θ=m θ) →
    ∀ p : ℝ,1≤p →
      RealLpMultiplierBound (ENNReal.ofReal p) m (∫ x,‖K x‖)

theorem continuousCutoff_norm_one (a θ : ℝ) :
    ‖Complex.ofReal (sourceArcCutoff (a*θ))‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact sourceArcCutoff_le_one _

noncomputable def continuousCutoffSymbol (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun θ => Complex.ofReal (sourceArcCutoff (a*θ)))
    (complexSourceCutoff_smooth.continuous.comp (continuous_const.mul continuous_id))
    1 (continuousCutoff_norm_one a)

theorem continuousCutoffSymbol_apply (a θ : ℝ) :
    continuousCutoffSymbol a θ=Complex.ofReal (sourceArcCutoff (a*θ)) := rfl

theorem continuousCutoffMultiplier_Lp (HY : RawYoungMultiplierInput)
    {a : ℝ} (ha : 0<a) {p : ℝ} (hp : 1≤p) :
    RealLpMultiplierBound (ENNReal.ofReal p) (continuousCutoffSymbol a) cutoffL1Constant := by
  have h := HY (scaledCutoffKernel a) (scaledCutoffKernel_integrable ha)
    (continuousCutoffSymbol a) (scaledCutoffKernel_fourier ha) p hp
  rwa [scaledCutoffKernel_integral_norm ha] at h

end PrimeSquares
