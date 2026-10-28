import PrimeSquares.CompactCircleLift

open Finset
namespace PrimeSquares

noncomputable def integerPeriodSum (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℤ, f (x+k)

theorem integerPeriodSum_periodic (f : ℝ → ℂ) :
    Function.Periodic (integerPeriodSum f) 1 := by
  intro x
  have he := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => f (x+k))
  change (∑' k : ℤ, f (x+1+k)) = ∑' k : ℤ, f (x+k)
  convert he using 1
  congr 1
  funext k
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  congr 1
  ring

theorem integerPeriodSum_window (f : ℝ → ℂ)
    (hs : ∀ x, 1 ≤ |x| → f x = 0) {x : ℝ}
    (hx : x ∈ Set.Icc (-(1/2) : ℝ) (1/2)) :
    integerPeriodSum f x = compactPeriodWindow f x := by
  classical
  rw [integerPeriodSum, tsum_eq_sum (s := {(-1 : ℤ),0,1})]
  · norm_num [compactPeriodWindow, sub_eq_add_neg, add_assoc]
  · intro k hk
    apply hs
    have hk' : k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 := by simpa only [mem_insert, mem_singleton, not_or] using hk
    have hd : k ≤ -2 ∨ 2 ≤ k := by omega
    rcases hd with h | h
    · have h' : (k : ℝ) ≤ -2 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.2]
    · have h' : (2 : ℝ) ≤ k := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.1]

end PrimeSquares
