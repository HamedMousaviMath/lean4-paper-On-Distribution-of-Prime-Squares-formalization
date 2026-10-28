import PrimeSquares.RealLineFourierMultipliers
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem realLineMultiplier_symbol_sub (m n : BoundedContinuousFunction ℝ ℂ) (f : RealLineL2) :
    realLineMultiplier (m-n) f=realLineMultiplier m f-realLineMultiplier n f := by
  apply realLineFourier.injective
  rw [map_sub,realLineFourier_multiplier,realLineFourier_multiplier,realLineFourier_multiplier]
  apply Lp.ext
  filter_upwards [realLineMultiply_ae (m-n) (realLineFourier f),
    realLineMultiply_ae m (realLineFourier f),realLineMultiply_ae n (realLineFourier f),
    Lp.coeFn_sub (realLineMultiply m (realLineFourier f)) (realLineMultiply n (realLineFourier f))]
    with θ h1 h2 h3 h4
  simp only [Pi.sub_apply] at h4
  rw [h1,h4,h2,h3]
  change (m θ-n θ)*realLineFourier f θ=m θ*realLineFourier f θ-n θ*realLineFourier f θ
  ring

theorem realLpMultiplierBound_sub {p : ENNReal} (hp : 1≤p)
    {m n : BoundedContinuousFunction ℝ ℂ} {K L : ℝ} (hK : 0≤K) (hL : 0≤L)
    (hm : RealLpMultiplierBound p m K) (hn : RealLpMultiplierBound p n L) :
    RealLpMultiplierBound p (m-n) (K+L) := by
  intro f hf
  obtain ⟨hfm,hbm⟩ := hm f hf
  obtain ⟨hfn,hbn⟩ := hn f hf
  rw [realLineMultiplier_symbol_sub]
  have he := Lp.coeFn_sub (realLineMultiplier m f) (realLineMultiplier n f)
  refine ⟨(hfm.sub hfn).ae_eq he.symm,?_⟩
  rw [eLpNorm_congr_ae he]
  calc
    _ ≤ eLpNorm (realLineMultiplier m f : ℝ→ℂ) p volume+
        eLpNorm (realLineMultiplier n f : ℝ→ℂ) p volume := eLpNorm_sub_le hp
    _ ≤ ENNReal.ofReal K*eLpNorm (f : ℝ→ℂ) p volume+
        ENNReal.ofReal L*eLpNorm (f : ℝ→ℂ) p volume := add_le_add hbm hbn
    _ = _ := by rw [ENNReal.ofReal_add hK hL,add_mul]

end PrimeSquares
