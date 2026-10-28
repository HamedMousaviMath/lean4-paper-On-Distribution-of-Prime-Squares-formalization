import PrimeSquares.CircleCollarWindow

namespace PrimeSquares

theorem norm_three_sum_square (a b c : ℂ) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have ht : ‖a+b+c‖ ≤ ‖a‖+‖b‖+‖c‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hn := norm_nonneg (a+b+c)
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hc := norm_nonneg c
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

theorem compactPeriodWindow_square (f : ℝ → ℂ) (x : ℝ) :
    ‖compactPeriodWindow f x‖^2 ≤ 3*(‖f (x-1)‖^2+‖f x‖^2+‖f (x+1)‖^2) :=
  norm_three_sum_square _ _ _

end PrimeSquares
