import PrimeSquares.FirstCollarTailDecay

namespace PrimeSquares

theorem collarFactor_after_onset_square {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q θ : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (i : ℕ) (hi : annularCollarMask ((((2 : ℕ)^i*M : ℕ) : ℝ)) q Q θ ≠ 0) (j : ℕ) :
    ‖annularCollarFactor ((2 : ℕ)^(i+j)*M) (β (i+j)) q Q θ‖^2 ≤
      (4*q/(Real.pi*Q))^2*(1/16 : ℝ)^j := by
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (collarFactor_after_onset hM β hβ0 hβ1 hq hQ i hi j) 2
  have he : ((1/4 : ℝ)^j)^2=(1/16 : ℝ)^j := by
    rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  simpa only [mul_pow,he] using hh

end PrimeSquares
