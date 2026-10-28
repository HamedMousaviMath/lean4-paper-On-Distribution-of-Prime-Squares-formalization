import PrimeSquares.SourceOrdinaryCollarFamily
import PrimeSquares.SourceScaleLowEstimate

namespace PrimeSquares

theorem source_log_budget_dyadic {c : ℝ} (hc : 0 < c) {M : ℕ} (hM : 2 ≤ M) {Q : ℝ}
    (hlog : Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log M)) (j : ℕ) :
    Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log ((((2 : ℕ)^j*M : ℕ) : ℝ))) := by
  have hMN : M ≤ (2 : ℕ)^j*M := by
    have hh : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right M hh
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMNreal : (M : ℝ) ≤ (((2 : ℕ)^j*M : ℕ) : ℝ) := by exact_mod_cast hMN
  have ha : 0 ≤ min (c/7) 1/8 := by positivity
  have hl := Real.log_le_log hMpos hMNreal
  exact hlog.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) ha)

theorem source_cutoff_le_dyadic_radius {Q : ℝ} (hQ : 1 ≤ Q) (M j : ℕ) :
    Q ≤ sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q :=
  sourceMajorArcScale_cutoff_le hQ _

end PrimeSquares
