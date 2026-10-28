import PrimeSquares.AnnularModelDecay

namespace PrimeSquares

theorem dyadic_square_scale (M j : ℕ) :
    ((((2 : ℕ)^j*M : ℕ) : ℝ)^2)=(4 : ℝ)^j*(M : ℝ)^2 := by
  push_cast
  rw [mul_pow]
  congr 1
  rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
  norm_num

theorem dyadic_annular_frequency_decay {M : ℕ} (hM : 2 ≤ M) {β q Q θ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq : 0 < q) (hQ : 0 < Q)
    (hθ : Q/(2*q*(M : ℝ)^2) ≤ |θ|) (j : ℕ) :
    ‖annularOscillatoryModel ((2 : ℕ)^j*M) β θ‖ ≤ (4*q/(Real.pi*Q))*(1/4 : ℝ)^j := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hpow : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by norm_num)
  have hMj : 2 ≤ (2 : ℕ)^j*M := hM.trans (by simpa only [one_mul] using Nat.mul_le_mul_right M hpow)
  have he : (Q*(4 : ℝ)^j)/(2*q*((((2 : ℕ)^j*M : ℕ) : ℝ)^2))=Q/(2*q*(M : ℝ)^2) := by
    rw [dyadic_square_scale]
    field_simp
  have h := annularOscillatoryModel_outside_arc (N := (2 : ℕ)^j*M) (β := β)
    (q := 2*q) (R := Q*(4 : ℝ)^j) (θ := θ) hMj hβ0 hβ1
    (mul_pos (by norm_num : (0 : ℝ) < 2) hq) (mul_pos hQ (by positivity)) (by rw [he];exact hθ)
  convert h using 1
  simp only [one_div,inv_pow]
  field_simp
  norm_num

end PrimeSquares
