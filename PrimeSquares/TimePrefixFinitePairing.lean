import PrimeSquares.TimePrefixRademacherMenshov
open Finset
open scoped lp
namespace PrimeSquares
theorem time_prefix_finite_pairing (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) (S : Finset ℤ) :
    (∑ x ∈ S,timePrefixL2Majorant h a G x) ≤
      Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryNodeNormEnergy h a G)*Real.sqrt S.card := by
  simpa only [timePrefixL2Majorant_norm] using real_l2_finite_sum_bound S (timePrefixL2Majorant h a G)
    (fun x _ => timePrefixL2Majorant_nonneg h a G x)
end PrimeSquares
