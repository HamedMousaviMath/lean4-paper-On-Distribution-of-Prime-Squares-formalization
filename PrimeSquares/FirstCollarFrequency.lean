import PrimeSquares.FirstAnnularCollarScale

namespace PrimeSquares

theorem firstCollar_frequency {M : ℕ} (hM : 2 ≤ M) {q Q θ : ℝ}
    (hq : 0 < q) (hQ : 0 < Q) {i : ℕ}
    (hi : annularCollarMask ((((2 : ℕ)^i*M : ℕ) : ℝ)) q Q θ ≠ 0) :
    Q/(2*q*((((2 : ℕ)^i*M : ℕ) : ℝ)^2)) < |θ| := by
  have hn : (0 : ℝ) < (((2 : ℕ)^i*M : ℕ) : ℝ) := by exact_mod_cast (by have hh := dyadic_annular_scale_lower hM i;omega : 0 < (2 : ℕ)^i*M)
  exact annularCollarMask_onset hn hq hQ hi

theorem collarFactor_before_onset (M : ℕ) (β : ℕ → ℝ) (q Q θ : ℝ) (i : ℕ)
    (hi : ∀ j : ℕ,j < i → annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ=0) :
    ∀ j : ℕ,j < i → annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ=0 := by
  intro j hj
  exact annularCollarFactor_zero_of_mask _ _ _ _ _ (hi j hj)

end PrimeSquares
