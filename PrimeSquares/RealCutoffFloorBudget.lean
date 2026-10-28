import PrimeSquares.RealOrdinaryLowModel

namespace PrimeSquares

theorem floor_cutoff_two {Q : ℝ} (hQ : 2 ≤ Q) : 2 ≤ ⌊Q⌋₊ := by
  exact Nat.le_floor hQ

theorem floor_cutoff_log {Q : ℝ} (hQ : 1 ≤ Q) :
    Real.log ((⌊Q⌋₊ : ℝ)+1) ≤ Real.log (2*Q) := by
  have hf := Nat.floor_le (by linarith : (0 : ℝ) ≤ Q)
  exact Real.log_le_log (by positivity) (by linarith)

theorem real_cutoff_denominator_bound {Q : ℝ} (hQ : 0 ≤ Q) {q : ℕ} (hq : q ≤ ⌊Q⌋₊) :
    (q : ℝ) ≤ Q := (by exact_mod_cast hq : (q : ℝ) ≤ ⌊Q⌋₊).trans (Nat.floor_le hQ)

end PrimeSquares
