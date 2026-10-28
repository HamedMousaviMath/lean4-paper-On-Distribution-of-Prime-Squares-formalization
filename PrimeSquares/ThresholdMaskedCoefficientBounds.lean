import PrimeSquares.ThresholdEnvelopeBounds
import PrimeSquares.RationalRelativeCutoffSum

namespace PrimeSquares

theorem relativeCutoffProfile_small {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (ht1 : t ≤ 1) :
    relativeCutoffProfile δ t=t^δ := by
  apply min_eq_left
  exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)

theorem relativeCutoffProfile_large {δ t : ℝ} (hδ : 0 ≤ δ) (ht1 : 1 ≤ t) :
    relativeCutoffProfile δ t=t^(-δ) := by
  apply min_eq_right
  exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)

theorem inverse_sqrt_relative {d B Q : ℝ} (hd : 0 < d) (hB : 0 < B) (hQ : 0 < Q) :
    d^(-(1/2 : ℝ))=B^(1/2 : ℝ)*Q^(-(1/2 : ℝ))*(d*B/Q)^(-(1/2 : ℝ)) := by
  have hb : B^(1/2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hB _).ne'
  have hq : Q^(1/2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hQ _).ne'
  rw [Real.div_rpow (mul_nonneg hd.le hB.le) hQ.le,Real.mul_rpow hd.le hB.le,
    Real.rpow_neg hd.le,Real.rpow_neg hB.le,Real.rpow_neg hQ.le]
  field_simp

theorem conductorRho_scaled_threshold_large (d : ℕ) (hd : 0 < d) {B Q : ℝ}
    (hB : 1 ≤ B) (hQ : 0 < Q) (hL : 2 ≤ Real.log Q)
    (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4) (ht : 1 ≤ (d : ℝ)*B/Q) :
    conductorRho d ≤ Real.exp (gaussAnalyticMajorant (Real.log Q))*((d : ℝ)*B/Q)^(1/4 : ℝ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have he : 0 ≤ Real.exp (gaussAnalyticMajorant (Real.log Q)) := (Real.exp_pos _).le
  by_cases hsmall : (d : ℝ) ≤ Q
  · have hp : (1 : ℝ) ≤ ((d : ℝ)*B/Q)^(1/4 : ℝ) :=
      Real.one_le_rpow ht (by norm_num)
    exact (conductorRho_threshold_small d hd hQ hL hsmall).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp he)
  · have hbase : (d : ℝ)/Q ≤ (d : ℝ)*B/Q :=
      div_le_div_of_nonneg_right (by nlinarith) hQ.le
    exact (conductorRho_threshold_large d hd hQ hL hSlope (le_of_not_ge hsmall)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase (by norm_num)) he)

theorem threshold_masked_product (d : ℕ) (hd : 0 < d) {B Q A K : ℝ}
    (hB : 1 ≤ B) (hQ : 0 < Q) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (c f : ℂ) (hc : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*conductorRho d)
    (hf : ‖f‖ ≤ K) (hfl : ‖f‖ ≤ K*((d : ℝ)*B/Q)) :
    ‖c*f‖ ≤ (A*K*B^(1/2 : ℝ)*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)))*
      relativeCutoffProfile (1/4) ((d : ℝ)*B/Q) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hBp : 0 < B := by linarith
  let t : ℝ := (d : ℝ)*B/Q
  let E : ℝ := Real.exp (gaussAnalyticMajorant (Real.log Q))
  let D : ℝ := A*K*B^(1/2 : ℝ)*Q^(-(1/2 : ℝ))*E
  have ht : 0 < t := by dsimp [t];positivity
  have hE : 0 < E := Real.exp_pos _
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hid : (d : ℝ)^(-(1/2 : ℝ))=B^(1/2 : ℝ)*Q^(-(1/2 : ℝ))*t^(-(1/2 : ℝ)) :=
    inverse_sqrt_relative hdr hBp hQ
  change ‖c*f‖ ≤ D*relativeCutoffProfile (1/4) t
  rw [norm_mul]
  by_cases ht1 : t ≤ 1
  · have hdQ : (d : ℝ) ≤ Q := by
      have hm : (d : ℝ)*B ≤ Q := (div_le_one hQ).mp ht1
      nlinarith
    have hrho : conductorRho d ≤ E := conductorRho_threshold_small d hd hQ hL hdQ
    have hc' : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*E := hc.trans
      (mul_le_mul_of_nonneg_left hrho (by positivity))
    have hpow : t^(-(1/2 : ℝ))*t=t^(1/2 : ℝ) := by
      calc
        _ = t^(-(1/2 : ℝ))*t^(1 : ℝ) := by rw [Real.rpow_one]
        _ = t^(-(1/2 : ℝ)+1) := (Real.rpow_add ht _ _).symm
        _ = _ := by norm_num
    calc
      _ ≤ (A*(d : ℝ)^(-(1/2 : ℝ))*E)*(K*t) := mul_le_mul hc' hfl (norm_nonneg _) (by positivity)
      _ = D*(t^(-(1/2 : ℝ))*t) := by rw [hid];dsimp [D];ring
      _ = D*t^(1/2 : ℝ) := by rw [hpow]
      _ ≤ D*t^(1/4 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)) hD
      _ = _ := by rw [relativeCutoffProfile_small (by norm_num : (0 : ℝ) ≤ 1/4) ht ht1]
  · have h1t : 1 ≤ t := (lt_of_not_ge ht1).le
    have hrho : conductorRho d ≤ E*t^(1/4 : ℝ) :=
      conductorRho_scaled_threshold_large d hd hB hQ hL hSlope h1t
    have hc' : ‖c‖ ≤ A*(d : ℝ)^(-(1/2 : ℝ))*(E*t^(1/4 : ℝ)) := hc.trans
      (mul_le_mul_of_nonneg_left hrho (by positivity))
    have hpow : t^(-(1/2 : ℝ))*t^(1/4 : ℝ)=t^(-(1/4 : ℝ)) := by
      rw [←Real.rpow_add ht]
      norm_num
    calc
      _ ≤ (A*(d : ℝ)^(-(1/2 : ℝ))*(E*t^(1/4 : ℝ)))*K :=
        mul_le_mul hc' hf (norm_nonneg _) (by positivity)
      _ = D*(t^(-(1/2 : ℝ))*t^(1/4 : ℝ)) := by rw [hid];dsimp [D];ring
      _ = D*t^(-(1/4 : ℝ)) := by rw [hpow]
      _ = _ := by rw [relativeCutoffProfile_large (by norm_num : (0 : ℝ) ≤ 1/4) h1t]

end PrimeSquares
