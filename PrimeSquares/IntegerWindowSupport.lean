import PrimeSquares.RationalHighWeightedSum
import PrimeSquares.CompactPeriodSum

namespace PrimeSquares

theorem integerPeriodSum_unit_window (f : ℝ → ℂ) (hs : ∀ x,1 ≤ |x| → f x=0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    integerPeriodSum f x=compactPeriodWindow f x := by
  classical
  rw [integerPeriodSum,tsum_eq_sum (s := {(-1 : ℤ),0,1})]
  · norm_num [compactPeriodWindow,sub_eq_add_neg,add_assoc]
  · intro k hk
    apply hs
    have hk' : k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hk
    have hd : k ≤ -2 ∨ 2 ≤ k := by omega
    rcases hd with h | h
    · have h' : (k : ℝ) ≤ -2 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.2]
    · have h' : (2 : ℝ) ≤ k := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.1]

end PrimeSquares
