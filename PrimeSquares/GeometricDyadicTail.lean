import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum

namespace PrimeSquares

theorem dyadic_ninth_geometric : HasSum (fun j : ℕ => ((1/512 : ℝ)^j)) (512/511 : ℝ) := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := (1/512 : ℝ)) (by norm_num)
  convert h using 1; norm_num

theorem dyadic_ninth_partial_bound (J : ℕ) :
    (∑ j ∈ Finset.range J, ((1/512 : ℝ)^j)) ≤ 512/511 := by
  exact (dyadic_ninth_geometric.summable.sum_le_tsum (Finset.range J)
    (fun j _ => by positivity)).trans_eq dyadic_ninth_geometric.tsum_eq

end PrimeSquares
