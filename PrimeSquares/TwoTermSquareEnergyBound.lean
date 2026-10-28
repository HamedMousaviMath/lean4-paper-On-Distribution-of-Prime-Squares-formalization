import PrimeSquares.SharpHighLeadingTwoRepair
namespace PrimeSquares
theorem norm_sub_square_two_bound (a b : ℂ) : ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have ht := norm_sub_le a b
  have hs := sq_nonneg (‖a‖-‖b‖)
  nlinarith [norm_nonneg (a-b),norm_nonneg a,norm_nonneg b]
end PrimeSquares
