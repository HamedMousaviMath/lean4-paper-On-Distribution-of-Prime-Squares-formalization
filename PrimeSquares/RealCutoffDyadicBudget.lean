import PrimeSquares.GrowingGeometricBudget

namespace PrimeSquares

theorem real_cutoff_log2_power {Q : ℝ} (hQ : 1 ≤ Q) :
    (2 : ℝ)^(Nat.log2 ⌊Q⌋₊) ≤ Q := by
  have hf : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hQ)
  have hn := Nat.log2_self_le (n := ⌊Q⌋₊) (by omega : ⌊Q⌋₊ ≠ 0)
  have hc : (2 : ℝ)^(Nat.log2 ⌊Q⌋₊) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hn
  exact hc.trans (Nat.floor_le (by linarith))

theorem real_cutoff_growing_power {Q δ : ℝ} (hQ : 1 ≤ Q) (hδ : δ ≤ 1) :
    ((2 : ℝ)^(1-δ))^(Nat.log2 ⌊Q⌋₊) ≤ Q^(1-δ) := by
  have he : ((2 : ℝ)^(1-δ))^(Nat.log2 ⌊Q⌋₊)=((2 : ℝ)^(Nat.log2 ⌊Q⌋₊))^(1-δ) := by
    calc
      _ = (2 : ℝ)^((1-δ)*(Nat.log2 ⌊Q⌋₊ : ℝ)) := (Real.rpow_mul_natCast (by norm_num) (1-δ) _).symm
      _ = (2 : ℝ)^((Nat.log2 ⌊Q⌋₊ : ℝ)*(1-δ)) := by congr 1;ring
      _ = _ := Real.rpow_natCast_mul (by norm_num) _ (1-δ)
  rw [he]
  exact Real.rpow_le_rpow (by positivity) (real_cutoff_log2_power hQ) (sub_nonneg.mpr hδ)

end PrimeSquares
