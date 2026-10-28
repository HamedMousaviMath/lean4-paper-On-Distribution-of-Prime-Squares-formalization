import PrimeSquares.BadnessSpacingLimits

set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
namespace PrimeSquares

theorem badnessThickeningDeficit_ratio_zero (HW : RawSplitQuadraticWeilInput) :
    Tendsto (fun γ : ℝ => badnessThickeningDeficit γ/γ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hpos : ∀ᶠ γ : ℝ in 𝓝[>] (0:ℝ), 0 < γ := self_mem_nhdsWithin
  have hsmall : ∀ᶠ γ : ℝ in 𝓝[>] (0:ℝ), γ < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    (tendsto_id : Tendsto (fun γ : ℝ => γ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun γ : ℝ => (3/2:ℝ)*γ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hid.const_mul (3/2:ℝ)
  have hlower : ∀ᶠ γ : ℝ in 𝓝[>] (0:ℝ), 0 ≤ badnessThickeningDeficit γ/γ := by
    filter_upwards [hpos,hsmall] with γ hγ hγ1
    exact div_nonneg (badnessThickeningDeficit_bounds HW γ hγ hγ1.le).1 hγ.le
  have hupper : ∀ᶠ γ : ℝ in 𝓝[>] (0:ℝ), badnessThickeningDeficit γ/γ ≤ (3/2:ℝ)*γ := by
    filter_upwards [hpos,hsmall] with γ hγ hγ1
    apply (div_le_iff₀ hγ).mpr
    nlinarith [(badnessThickeningDeficit_bounds HW γ hγ hγ1.le).2]
  exact squeeze_zero' hlower hupper hlim

theorem badness_thickening_little_o (HW : RawSplitQuadraticWeilInput) :
    badnessThickeningDeficit =o[𝓝[>] (0:ℝ)] (fun γ : ℝ => γ) := by
  have hpos : ∀ᶠ γ : ℝ in 𝓝[>] (0:ℝ), 0 < γ := self_mem_nhdsWithin
  have hgf : ∀ᶠ γ : ℝ in 𝓝[>] (0:ℝ), γ=0 → badnessThickeningDeficit γ=0 := by
    filter_upwards [hpos] with γ hγ
    intro hz
    exact False.elim ((ne_of_gt hγ) hz)
  exact (Asymptotics.isLittleO_iff_tendsto' hgf).mpr (badnessThickeningDeficit_ratio_zero HW)

end PrimeSquares
