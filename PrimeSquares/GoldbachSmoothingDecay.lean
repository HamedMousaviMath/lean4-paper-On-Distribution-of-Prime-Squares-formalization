import PrimeSquares.GoldbachSingularIntegralNorm

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_smoothing_power_identity {t c : ℝ} (ht : 0<t) (hc : 0<c) :
    (t/c)^2/(Real.sqrt t*t)=Real.sqrt t/c^2 := by
  let s := Real.sqrt t
  have hs : 0<s := Real.sqrt_pos.mpr ht
  have he : s^2=t := Real.sq_sqrt ht.le
  calc
    _=(s^2/c)^2/(s*s^2) := by rw [he]
    _=s/c^2 := by field_simp

theorem goldbach_smoothing_decay_integrable (w f : ℝ→ℂ)
    (hw : StronglyMeasurable w) (hf : StronglyMeasurable f)
    {c K D : ℝ} (hc : 0<c) (hK : 0≤K) (hD : 0≤D)
    (hweight : ∀ t : ℝ,‖w t‖≤K*min 1 ((|t|/c)^2))
    (hdecay : ∀ t : ℝ,t≠0 →‖f t‖≤D/(Real.sqrt |t| * |t|)) :
    Integrable (fun t=>w t*f t) ∧
      (∫ t : ℝ,‖w t*f t‖)≤6*K*D/Real.sqrt c := by
  have hKD : 0≤K*D := mul_nonneg hK hD
  have hnear (t : ℝ) (htc : |t|≤c) : ‖w t*f t‖≤K*D*Real.sqrt c/c^2 := by
    by_cases ht : t=0
    · subst t
      have hw0 : w 0=0 := norm_le_zero_iff.mp (by simpa only [abs_zero,zero_div,zero_pow (by decide : 2≠0),min_eq_right zero_le_one,mul_zero] using hweight 0)
      rw [hw0,zero_mul,norm_zero]
      positivity
    · have htp : 0 < |t| := abs_pos.mpr ht
      rw [norm_mul]
      calc
        _≤(K*(|t|/c)^2)*(D/(Real.sqrt |t| * |t|)) := mul_le_mul
          ((hweight t).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK))
          (hdecay t ht) (norm_nonneg _) (by positivity)
        _=(K*D)*((|t|/c)^2/(Real.sqrt |t| * |t|)) := by ring
        _=K*D*Real.sqrt |t|/c^2 := by rw [goldbach_smoothing_power_identity htp hc];ring
        _≤_ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htc) hKD) (sq_nonneg _)
  have hfar (t : ℝ) (htc : c < |t|) : ‖w t*f t‖≤(K*D)*|t|^(-(3/2:ℝ)) := by
    have ht : t≠0 := abs_pos.mp (hc.trans htc)
    rw [norm_mul]
    calc
      _≤K*(D/(Real.sqrt |t| * |t|)) := mul_le_mul
        ((hweight t).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) ((|t|/c)^2)) hK))
        (hdecay t ht) (norm_nonneg _) hK
      _=(K*D)*(Real.sqrt |t| * |t|)⁻¹ := by ring
      _=_ := by rw [goldbach_inverse_sqrt_power (hc.trans htc)]
  have hi := goldbach_two_sided_integrable_decay (fun t=>w t*f t) (hw.mul hf) hc hKD hnear hfar
  refine ⟨hi.1,hi.2.trans_eq ?_⟩
  have hs := Real.sqrt_pos.mpr hc
  have he := Real.sq_sqrt hc.le
  field_simp
  nlinarith [sq_nonneg (K*D)]

end PrimeSquares
