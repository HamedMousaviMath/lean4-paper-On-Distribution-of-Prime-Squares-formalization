import PrimeSquares.DilatedCutoffGeometry

namespace PrimeSquares

theorem narrowCutoff_inside_broad_core {N q R Q θ : ℝ} {s : ℕ}
    (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q) (hqR : q ≤ R) (hQR : Q ≤ R)
    (hs : (2 : ℝ)^s ≤ q) (hb : 2*R^4 ≤ N^2)
    (hn : sourceArcCutoff ((q*N^2/Q)*θ) ≠ 0) : sourceArcCutoffScale s θ = 1 := by
  have ha : 0 < q*N^2/Q := by positivity
  have hr := dilatedSourceCutoff_radius ha hn
  have he : 1/(q*N^2/Q) = Q/(q*N^2) := by field_simp
  rw [he] at hr
  exact sourceArcCutoffScale_major_arc hN hq hqR hs hb
    (hr.le.trans (div_le_div_of_nonneg_right hQR (by positivity)))

theorem narrowCutoff_mul_broad {N q R Q θ : ℝ} {s : ℕ}
    (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q) (hqR : q ≤ R) (hQR : Q ≤ R)
    (hs : (2 : ℝ)^s ≤ q) (hb : 2*R^4 ≤ N^2) :
    sourceArcCutoff ((q*N^2/Q)*θ)*sourceArcCutoffScale s θ =
      sourceArcCutoff ((q*N^2/Q)*θ) := by
  by_cases hz : sourceArcCutoff ((q*N^2/Q)*θ) = 0
  · rw [hz,zero_mul]
  · rw [narrowCutoff_inside_broad_core hN hq hQ hqR hQR hs hb hz,mul_one]

end PrimeSquares
