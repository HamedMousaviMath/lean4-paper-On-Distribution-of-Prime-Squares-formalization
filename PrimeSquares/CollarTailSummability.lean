import PrimeSquares.FirstCollarTailSquares

namespace PrimeSquares

theorem collarFactor_tail_square_summable {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q θ : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (i : ℕ) (hi : annularCollarMask ((((2 : ℕ)^i*M : ℕ) : ℝ)) q Q θ ≠ 0) :
    Summable (fun j : ℕ => ‖annularCollarFactor ((2 : ℕ)^(i+j)*M) (β (i+j)) q Q θ‖^2) := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (1/16 : ℝ)) (by norm_num)
  exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (collarFactor_after_onset_square hM β hβ0 hβ1 hq hQ i hi) (hg.summable.mul_left _)

theorem collarFactor_tail_square_total {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q θ : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (i : ℕ) (hi : annularCollarMask ((((2 : ℕ)^i*M : ℕ) : ℝ)) q Q θ ≠ 0) :
    (∑' j : ℕ,‖annularCollarFactor ((2 : ℕ)^(i+j)*M) (β (i+j)) q Q θ‖^2) ≤
      (16/15 : ℝ)*(4*q/(Real.pi*Q))^2 := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (1/16 : ℝ)) (by norm_num)
  have hs := collarFactor_tail_square_summable hM β hβ0 hβ1 hq hQ i hi
  calc
    _ ≤ ∑' j : ℕ,(4*q/(Real.pi*Q))^2*(1/16 : ℝ)^j :=
      hs.tsum_le_tsum (collarFactor_after_onset_square hM β hβ0 hβ1 hq hQ i hi) (hg.summable.mul_left _)
    _ = _ := by rw [tsum_mul_left,hg.tsum_eq];norm_num;ring

end PrimeSquares
