import PrimeSquares.TemporalMaximumConvergence
open Finset
open scoped lp
namespace PrimeSquares
theorem temporalMaximum_finite_spatial_energy (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (_hB : 0 ≤ B)
    (hF : FiniteTemporalMajorants F B) (S : Finset ℤ) :
    (∑ x ∈ S,(⨆ j : ℕ,‖F j x‖)^2) ≤ B^2 := by
  have hc := tendsto_finsetSum S (fun x _ => (initialTemporalMaximum_tendsto F hF x).pow 2)
  apply le_of_tendsto hc
  apply Filter.Eventually.of_forall
  intro n
  have he := lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (initialTemporalMaximumL2 F hF n) S
  have ht : (∑ x ∈ S,(initialTemporalMaximum F n x)^2) ≤ ‖initialTemporalMaximumL2 F hF n‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,initialTemporalMaximumL2] using he
  exact ht.trans (pow_le_pow_left₀ (norm_nonneg _) (initialTemporalMaximumL2_norm F hF n) 2)
end PrimeSquares
