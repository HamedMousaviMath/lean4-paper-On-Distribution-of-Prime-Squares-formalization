import PrimeSquares.FullCollarSquareTotal

namespace PrimeSquares

theorem collarFactor_finite_square_energy {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (J : Finset ℕ) (θ : ℝ) :
    (∑ j ∈ J,‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2) ≤
      (16/15 : ℝ)*(4*q/(Real.pi*Q))^2 :=
  ((collarFactor_square_summable hM β hβ0 hβ1 hq hQ θ).sum_le_tsum J (fun _ _ => sq_nonneg _)).trans
    (collarFactor_square_total hM β hβ0 hβ1 hq hQ θ)

theorem collarFactor_finite_square_simple {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (J : Finset ℕ) (θ : ℝ) :
    (∑ j ∈ J,‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2) ≤ (8*q/(Real.pi*Q))^2 := by
  have hh := collarFactor_finite_square_energy hM β hβ0 hβ1 hq hQ J θ
  have he : (8*q/(Real.pi*Q))^2=4*(4*q/(Real.pi*Q))^2 := by ring
  rw [he]
  nlinarith [sq_nonneg (4*q/(Real.pi*Q))]

end PrimeSquares
