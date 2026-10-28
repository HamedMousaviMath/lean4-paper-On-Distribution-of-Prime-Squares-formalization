import PrimeSquares.ThresholdMaskedCoefficientBounds

namespace PrimeSquares

noncomputable def sharpThresholdAmplitude (A B Q : ℝ) : ℝ :=
  A*B^(1/2 : ℝ)*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q))

theorem sharpThresholdAmplitude_nonneg {A B Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q) :
    0 ≤ sharpThresholdAmplitude A B Q := by unfold sharpThresholdAmplitude;positivity

theorem threshold_coefficient_small (d : ℕ) (hd : 0<d) {A B Q t : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hL : 2 ≤ Real.log Q)
    (c : ℂ) (hc : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*conductorRho d)
    (ht : t=(d : ℝ)*B/Q) (ht1 : t ≤ 1) :
    ‖c‖ ≤ sharpThresholdAmplitude A B Q*t^(-(1/2 : ℝ)) := by
  have hdr : (0 : ℝ)<d := by exact_mod_cast hd
  have hBp : 0<B := by linarith
  have hdQ : (d : ℝ) ≤ Q := by
    have hm : (d : ℝ)*B ≤ Q := (div_le_one hQ).mp (ht ▸ ht1)
    nlinarith
  have hrho := conductorRho_threshold_small d hd hQ hL hdQ
  calc
    _ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)) :=
      hc.trans (mul_le_mul_of_nonneg_left hrho (by positivity))
    _ = _ := by rw [inverse_sqrt_relative hdr hBp hQ,ht];unfold sharpThresholdAmplitude;ring

theorem threshold_coefficient_large (d : ℕ) (hd : 0<d) {A B Q t : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hL : 2 ≤ Real.log Q)
    (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (c : ℂ) (hc : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*conductorRho d)
    (ht : t=(d : ℝ)*B/Q) (ht1 : 1 ≤ t) :
    ‖c‖ ≤ sharpThresholdAmplitude A B Q*t^(-(1/4 : ℝ)) := by
  have hh := threshold_masked_product d hd hB hQ hA (by norm_num : (0 : ℝ) ≤ 1)
    hL hSlope c 1 hc (by norm_num : ‖(1 : ℂ)‖ ≤ (1 : ℝ))
    (by simpa only [norm_one,one_mul,←ht] using ht1)
  simpa only [mul_one,←ht,relativeCutoffProfile_large (by norm_num : (0 : ℝ) ≤ 1/4) ht1,
    sharpThresholdAmplitude] using hh

theorem threshold_small_block_amplitude (d : ℕ) (hd : 0<d) {A B Q t u : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hL : 2 ≤ Real.log Q)
    (c : ℂ) (hc : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*conductorRho d)
    (ht : t=(d : ℝ)*B/Q) (ht1 : t ≤ 1) (hu : 0<u) (hut : u ≤ t) :
    ‖c‖ ≤ sharpThresholdAmplitude A B Q*u^(-(1/2 : ℝ)) :=
  (threshold_coefficient_small d hd hA hB hQ hL c hc ht ht1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu hut (by norm_num))
      (sharpThresholdAmplitude_nonneg hA (by linarith) hQ.le))

theorem threshold_large_block_amplitude (d : ℕ) (hd : 0<d) {A B Q t u : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hL : 2 ≤ Real.log Q)
    (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (c : ℂ) (hc : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*conductorRho d)
    (ht : t=(d : ℝ)*B/Q) (ht1 : 1 ≤ t) (hu : 0<u) (hut : u ≤ t) :
    ‖c‖ ≤ sharpThresholdAmplitude A B Q*min 1 (u^(-(1/4 : ℝ))) := by
  have hh := threshold_coefficient_large d hd hA hB hQ hL hSlope c hc ht ht1
  have htpos : 0<t := by linarith
  have ha := sharpThresholdAmplitude_nonneg hA (by linarith : (0 : ℝ) ≤ B) hQ.le
  rw [mul_min_of_nonneg _ _ ha]
  apply le_min
  · have hp := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num : -(1/4 : ℝ) ≤ 0)
    simpa only [mul_one] using hh.trans (mul_le_mul_of_nonneg_left hp ha)
  · exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hu hut (by norm_num)) ha)

theorem large_amplitude_profile {t : ℝ} (ht : 1/2 ≤ t) :
    min 1 (t^(-(1/4 : ℝ))) ≤ (2 : ℝ)^(1/4 : ℝ)*relativeCutoffProfile (1/4) t := by
  have htp : 0<t := by linarith
  by_cases hsmall : t ≤ 1
  · rw [relativeCutoffProfile_small (by norm_num : (0 : ℝ) ≤ 1/4) htp hsmall]
    have h := Real.one_le_rpow (by linarith : (1 : ℝ) ≤ 2*t) (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htp.le] at h
    exact (min_le_left _ _).trans h
  · have ht1 : 1 ≤ t := (lt_of_not_ge hsmall).le
    rw [relativeCutoffProfile_large (by norm_num : (0 : ℝ) ≤ 1/4) ht1]
    exact (min_le_right _ _).trans (le_mul_of_one_le_left (by positivity)
      (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)))

theorem small_amplitude_profile {t : ℝ} (ht : 0<t) (ht1 : t ≤ 1) :
    t^(-(1/2 : ℝ))*(2*t) ≤ 2*relativeCutoffProfile (1/4) t := by
  have he : t^(-(1/2 : ℝ))*t=t^(1/2 : ℝ) := by
    calc
      _=t^(-(1/2 : ℝ))*t^(1 : ℝ) := by rw [Real.rpow_one]
      _=t^(-(1/2 : ℝ)+1) := (Real.rpow_add ht _ _).symm
      _=_ := by norm_num
  rw [relativeCutoffProfile_small (by norm_num : (0 : ℝ) ≤ 1/4) ht ht1]
  calc
    _=2*t^(1/2 : ℝ) := by nlinarith only [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (1/4 : ℝ) ≤ 1/2)) (by norm_num)

end PrimeSquares
