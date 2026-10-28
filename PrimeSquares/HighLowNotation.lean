import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The paper's logarithmic and Orlicz conventions

Source: `e:Lognotation`, `e:defPhi`, used in Theorem 4.1.
The definitions retain the additive twos in both logarithms. Their source
domain is x>0; the Lean functions have harmless total extensions elsewhere.
-/

namespace PrimeSquares

noncomputable def paperLog (x : ℝ) : ℝ := 2 + |Real.log x|

noncomputable def paperLogLog (x : ℝ) : ℝ := 2 + Real.log (paperLog x)

noncomputable def paperPhi (c κ x : ℝ) : ℝ :=
  Real.exp (c * (paperLog x) ^ κ / paperLogLog x)

theorem paperLog_two_le (x : ℝ) : 2 ≤ paperLog x := by
  dsimp only [paperLog]
  linarith [abs_nonneg (Real.log x)]

theorem paperLog_pos (x : ℝ) : 0 < paperLog x := lt_of_lt_of_le (by norm_num) (paperLog_two_le x)

theorem paperLogLog_two_le (x : ℝ) : 2 ≤ paperLogLog x := by
  have h := Real.log_nonneg (show 1 ≤ paperLog x by have := paperLog_two_le x; linarith)
  dsimp only [paperLogLog]
  linarith

theorem paperLogLog_pos (x : ℝ) : 0 < paperLogLog x :=
  lt_of_lt_of_le (by norm_num) (paperLogLog_two_le x)

theorem paperLog_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    paperLog x = 2 - Real.log x := by
  rw [paperLog, abs_of_nonpos (Real.log_nonpos hx.le hx1)]
  ring

theorem paperLog_exp_neg (t : ℝ) (ht : 0 ≤ t) : paperLog (Real.exp (-t)) = 2 + t := by
  rw [paperLog, Real.log_exp, abs_of_nonpos (by linarith : -t ≤ 0)]
  ring

theorem paperPhi_pos (c κ x : ℝ) : 0 < paperPhi c κ x := Real.exp_pos _

theorem paperPhi_one_le {c : ℝ} (hc : 0 ≤ c) (κ x : ℝ) : 1 ≤ paperPhi c κ x := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (mul_nonneg hc (Real.rpow_nonneg (paperLog_pos x).le _))
    (paperLogLog_pos x).le

/-- The chosen dyadic scale is rounded down, preserving an upper cutoff. -/
theorem exists_dyadic_below {T : ℝ} (hT : 2 ≤ T) :
    ∃ k : ℕ, 2 ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ T ∧ T < 2 * (2 : ℝ) ^ k := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ T by linarith) (by norm_num : (1 : ℝ) < 2)
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, zero_add, pow_one] at hk'
    linarith
  refine ⟨k, ?_, hk, ?_⟩
  · simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ k by omega)
  · simpa only [pow_succ, mul_comm] using hk'

end PrimeSquares
