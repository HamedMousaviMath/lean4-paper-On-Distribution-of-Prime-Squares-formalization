import PrimeSquares.FirstCollarFrequency

namespace PrimeSquares

theorem collarFactor_after_onset {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q θ : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (i : ℕ) (hi : annularCollarMask ((((2 : ℕ)^i*M : ℕ) : ℝ)) q Q θ ≠ 0) (j : ℕ) :
    ‖annularCollarFactor ((2 : ℕ)^(i+j)*M) (β (i+j)) q Q θ‖ ≤
      (4*q/(Real.pi*Q))*(1/4 : ℝ)^j := by
  have hf := (firstCollar_frequency hM hq hQ hi).le
  have hh := dyadic_annular_frequency_decay (dyadic_annular_scale_lower hM i)
    (hβ0 (i+j)) (hβ1 (i+j)) hq hQ hf j
  rw [←dyadic_annular_scale_shift M i j] at hh
  exact (annularCollarFactor_le_annular _ _ _ _ _).trans hh

end PrimeSquares
