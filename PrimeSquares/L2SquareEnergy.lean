import PrimeSquares.CountableOperatorMaximum
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped lp
namespace PrimeSquares

theorem l2_square_hasSum (f : ℓ²(ℤ, ℂ)) : HasSum (fun x : ℤ => ‖f x‖^2) (‖f‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f

theorem l2_square_tsum (f : ℓ²(ℤ, ℂ)) : (∑' x : ℤ,‖f x‖^2)=‖f‖^2 := (l2_square_hasSum f).tsum_eq

theorem l2_square_finite_bound (f : ℓ²(ℤ, ℂ)) (S : Finset ℤ) : (∑ x ∈ S,‖f x‖^2) ≤ ‖f‖^2 :=
  ((l2_square_hasSum f).summable.sum_le_tsum S (fun x _ => sq_nonneg ‖f x‖)).trans_eq (l2_square_tsum f)

end PrimeSquares
