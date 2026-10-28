import PrimeSquares.RealLineFourierMultipliers
import PrimeSquares.QuantitativeIWParameters

set_option autoImplicit false
namespace PrimeSquares

/-- Independent general Riesz-Thorin interpolation theorem for the actual
linear real Fourier multiplier, on the L2 intersection. It contains no
annular, cutoff, IW, maximal or current-paper conclusion. -/
def RawRieszThorinMultiplierInput : Prop :=
  ∀ m : BoundedContinuousFunction ℝ ℂ,∀ p₀ p₁ p θ : ℝ,
    1≤ p₀ → 1≤ p₁ → 1≤ p → 0≤θ → θ≤1 →
    1/p=(1-θ)/p₀+θ/p₁ → ∀ K₀ K₁ : ℝ,0< K₀ → 0< K₁ →
    RealLpMultiplierBound (ENNReal.ofReal p₀) m K₀ →
    RealLpMultiplierBound (ENNReal.ofReal p₁) m K₁ →
    RealLpMultiplierBound (ENNReal.ofReal p) m (K₀^(1-θ)*K₁^θ)

theorem real_interpolate_one_two_at_iw (HRT : RawRieszThorinMultiplierInput)
    (m : BoundedContinuousFunction ℝ ℂ) {r : ℕ} (hr : 2≤ r)
    {K₀ K₂ : ℝ} (hK₀ : 0< K₀) (hK₂ : 0< K₂)
    (h1 : RealLpMultiplierBound 1 m K₀) (h2 : RealLpMultiplierBound 2 m K₂) :
    RealLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r)) m
      (K₀^(1-(r : ℝ)⁻¹)*K₂^((r : ℝ)⁻¹)) := by
  have hrR : (2 : ℝ)≤ r := by exact_mod_cast hr
  have hrp : (0 : ℝ)< r := by linarith
  have hp := iwNearOneExponent_bounds hr
  have hθ : (r : ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ (by linarith)
  have he : 1/iwNearOneExponent r=(1-(r : ℝ)⁻¹)/1+(r : ℝ)⁻¹/2 := by
    rw [iwNearOneExponent_reciprocal hr]
    field_simp
    ring
  have h := HRT m 1 2 (iwNearOneExponent r) (r : ℝ)⁻¹
    (by norm_num) (by norm_num) hp.1.le (inv_nonneg.mpr hrp.le) hθ he K₀ K₂ hK₀ hK₂
  norm_num only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] at h
  exact h h1 h2

end PrimeSquares
