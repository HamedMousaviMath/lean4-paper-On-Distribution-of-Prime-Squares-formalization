import PrimeSquares.AdmissibleLowFamilies
import PrimeSquares.CompactCirclePeriodization

namespace PrimeSquares

theorem source_low_width_budget {N Q R : ℝ} (hQ : 1 ≤ Q) (hQR : Q ≤ R)
    (hb : 2*R^4 ≤ N^2) : 2*Q ≤ N^2 := by
  have hR : 1 ≤ R := hQ.trans hQR
  have hs : R ≤ R^2 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ R) (by linarith : (0 : ℝ) ≤ R-1)]
  have hs' : 1 ≤ R^2 := by nlinarith
  have hf : R^2 ≤ R^4 := by nlinarith [mul_nonneg (sq_nonneg R) (by linarith : (0 : ℝ) ≤ R^2-1)]
  linarith

theorem circleAnnularCutoff_real (N : ℕ) (hN : 1 ≤ N) (β a : ℝ) (ha : 2 ≤ a) (ξ : ℝ) :
    circleAnnularCutoff N hN β a ha (ξ : PrimeCircle)=
      ∑' k : ℤ,annularOscillatoryModel N β (ξ+k)*Complex.ofReal (sourceArcCutoff (a*(ξ+k))) := by
  rw [circleAnnularCutoff,compactCircleLift_all_real]
  rfl

theorem circleAnnularCutoff_shift_real (N : ℕ) (hN : 1 ≤ N) (β a : ℝ) (ha : 2 ≤ a) (r ξ : ℝ) :
    circleFrequencyShift (circleAnnularCutoff N hN β a ha) (r : PrimeCircle) (ξ : PrimeCircle)=
      ∑' k : ℤ,annularOscillatoryModel N β (ξ-r+k)*Complex.ofReal (sourceArcCutoff (a*(ξ-r+k))) := by
  change circleAnnularCutoff N hN β a ha ((ξ : PrimeCircle)-(r : PrimeCircle))=_
  rw [←AddCircle.coe_sub,circleAnnularCutoff_real]

end PrimeSquares
