import PrimeSquares.WeightedPowerInfiniteTail
import PrimeSquares.FiniteMaximalEnvelopeBound

open scoped lp
namespace PrimeSquares

theorem operator_norm_shift_summable {K s : ℝ} (_hK : 0 ≤ K) (hs : 2 ≤ s) (J : ℕ)
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ j : ℕ, ‖T (J+j)‖ ≤ K*((J+j : ℕ)+1 : ℝ)^(-s)) :
    Summable (fun j : ℕ => ‖T (J+j)‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) hT
  exact (weighted_power_shift_summable hs J).mul_left K

theorem operator_norm_shift_tsum_bound {K s : ℝ} (hK : 0 ≤ K) (hs : 2 ≤ s) (J : ℕ)
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ j : ℕ, ‖T (J+j)‖ ≤ K*((J+j : ℕ)+1 : ℝ)^(-s)) :
    (∑' j : ℕ, ‖T (J+j)‖) ≤ 2*K*((J : ℝ)+1)^(1-s) := by
  have hn := operator_norm_shift_summable hK hs J T hT
  have hw := (weighted_power_shift_summable hs J).mul_left K
  calc
    _ ≤ ∑' j : ℕ, K*((J+j : ℕ)+1 : ℝ)^(-s) := hn.tsum_le_tsum hT hw
    _ = K*(∑' j : ℕ, ((J+j : ℕ)+1 : ℝ)^(-s)) := tsum_mul_left
    _ ≤ K*(2*((J : ℝ)+1)^(1-s)) :=
      mul_le_mul_of_nonneg_left (weighted_power_infinite_tail hs J) hK
    _ = _ := by ring

theorem operator_shift_summable {K s : ℝ} (hK : 0 ≤ K) (hs : 2 ≤ s) (J : ℕ)
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ j : ℕ, ‖T (J+j)‖ ≤ K*((J+j : ℕ)+1 : ℝ)^(-s)) :
    Summable (fun j : ℕ => T (J+j)) :=
  (operator_norm_shift_summable hK hs J T hT).of_norm

end PrimeSquares
