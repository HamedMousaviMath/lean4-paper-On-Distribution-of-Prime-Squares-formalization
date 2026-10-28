import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Positivity of the final elementary sieve bracket

The proof of Lemma 9.24 reduces positivity to the bracket below.
This file proves that bracket is positive. It does not prove the integral
evaluation or the estimate for W(9/8), nor the stronger decimal bound 0.17.
-/

namespace PrimeSquares

noncomputable def sieveBracket : ℝ :=
  (2 * Real.sqrt 2 / 3) * Real.log 2 - 27 / 64

theorem sieve_bracket_positive : 0 < sieveBracket := by
  have hs : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hl)
  dsimp [sieveBracket]
  nlinarith

theorem scaled_sieve_bracket_positive (K : ℝ) (hK : 0 < K) :
    0 < K * sieveBracket :=
  mul_pos hK sieve_bracket_positive

end PrimeSquares
