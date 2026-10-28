import PrimeSquares.AnnularHighFactor

namespace PrimeSquares

theorem min_one_le_fractional_power {t η : ℝ} (ht : 0 < t) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    min 1 t ≤ t^η := by
  by_cases ht1 : t ≤ 1
  · rw [min_eq_right ht1]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hη1
  · rw [min_eq_left (le_of_not_ge ht1)]
    exact Real.one_le_rpow (le_of_not_ge ht1) hη0

theorem high_power_product {q Q δ η : ℝ} (hq : 0 < q) (hQ : 0 < Q) :
    q^(-δ)*(q/Q)^η=Q^(-η)*q^(-(δ-η)) := by
  rw [Real.div_rpow hq.le hQ.le]
  calc
    _ = Q^(-η)*(q^(-δ)*q^η) := by rw [Real.rpow_neg hQ.le];ring
    _ = _ := by rw [←Real.rpow_add hq,show -δ+η=-(δ-η) by ring]

theorem two_bounds_rpow_interpolate {a D q Q δ η : ℝ} (hD : 0 ≤ D) (hq : 0 < q) (hQ : 0 < Q)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hs : a ≤ D*q^(-δ)) (hl : a ≤ D*q^(-δ)*q/Q) :
    a ≤ D*Q^(-η)*q^(-(δ-η)) := by
  have hA : 0 ≤ D*q^(-δ) := mul_nonneg hD (Real.rpow_pos_of_pos hq _).le
  have hm : a ≤ D*q^(-δ)*min 1 (q/Q) := by
    by_cases ht : 1 ≤ q/Q
    · simpa only [min_eq_left ht,mul_one] using hs
    · rw [min_eq_right (le_of_not_ge ht)]
      convert hl using 1
      ring
  calc
    _ ≤ D*q^(-δ)*min 1 (q/Q) := hm
    _ ≤ D*q^(-δ)*(q/Q)^η := mul_le_mul_of_nonneg_left
      (min_one_le_fractional_power (div_pos hq hQ) hη0 hη1) hA
    _ = _ := by rw [mul_assoc,high_power_product hq hQ];ring

end PrimeSquares
