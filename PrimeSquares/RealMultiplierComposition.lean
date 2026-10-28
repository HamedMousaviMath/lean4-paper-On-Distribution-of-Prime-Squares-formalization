import PrimeSquares.RealLineFourierMultipliers

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem realLineMultiply_comp_apply (m n : BoundedContinuousFunction ℝ ℂ) (f : RealLineL2) :
    realLineMultiply m (realLineMultiply n f)=realLineMultiply (m*n) f := by
  apply Lp.ext
  filter_upwards [realLineMultiply_ae m (realLineMultiply n f),realLineMultiply_ae n f,
    realLineMultiply_ae (m*n) f] with θ h1 h2 h3
  rw [h1,h2,h3]
  change m θ*(n θ*f θ)=(m θ*n θ)*f θ
  ring

theorem realLineMultiplier_comp_apply (m n : BoundedContinuousFunction ℝ ℂ) (f : RealLineL2) :
    realLineMultiplier m (realLineMultiplier n f)=realLineMultiplier (m*n) f := by
  apply realLineFourier.injective
  rw [realLineFourier_multiplier,realLineFourier_multiplier,realLineFourier_multiplier,
    realLineMultiply_comp_apply]

theorem realLpMultiplierBound_mul {p : ENNReal} {m n : BoundedContinuousFunction ℝ ℂ}
    {K L : ℝ} (hK : 0≤K) (hm : RealLpMultiplierBound p m K)
    (hn : RealLpMultiplierBound p n L) : RealLpMultiplierBound p (m*n) (K*L) := by
  intro f hf
  obtain ⟨hfn,hbn⟩ := hn f hf
  obtain ⟨hfmn,hbmn⟩ := hm (realLineMultiplier n f) hfn
  rw [realLineMultiplier_comp_apply] at hfmn hbmn
  refine ⟨hfmn,hbmn.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal K*(ENNReal.ofReal L*eLpNorm (f : ℝ→ℂ) p volume) := by
      gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hK,mul_assoc]

end PrimeSquares
