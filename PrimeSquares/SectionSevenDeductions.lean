import PrimeSquares.RestrictedToModular
import PrimeSquares.ActualPositiveSquareFamilies
import PrimeSquares.NearOneMomentExponential
import PrimeSquares.HighLowRestrictedDistribution
import PrimeSquares.QuantitativeIWBalance

/-!
# Checked Section 7 deductions; the full analytic milestone remains open

`PositiveRestrictedGauge` is an internal hypothesis below. It is not
declared an independent external input, and has not been proved for the
three arithmetic families. Thus these theorems do not claim the source
Orlicz maximal theorem, its strong lp corollary or its ergodic corollary.
-/

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem section7_truncated_modular_finite_card (A : PositiveAverageFamily) {C R : ℝ}
    (hC : 0≤C) (hR : 0≤R) (H : PositiveRestrictedGauge A C R)
    (F : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ x,x∉F → f x=0)
    {level : ℝ} (hl : 0<level) :
    {x | level<positiveMaximal A f x}.Finite ∧
      ({x | level<positiveMaximal A f x}.ncard : ℝ)≤
        (R*layerGaugeConstant C (2*A.mass))*
          ∑ x∈F.filter (fun x => level/(2*A.mass)<‖f x‖),nearOnePsi (9*C+4) (‖f x‖/level) := by
  have h := positiveRestricted_to_truncated_modular A hC hR H F f hf hl
  exact ⟨testedDistribution_finite h,testedDistribution_ncard h⟩

theorem section7_modular_deduction (A : PositiveAverageFamily) {C R : ℝ}
    (hC : 0≤C) (hR : 0≤R) (H : PositiveRestrictedGauge A C R)
    (F : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ x,x∉F → f x=0)
    {level : ℝ} (hl : 0<level) :
    TestedDistributionBound (positiveMaximal A f) level
      ((R*layerGaugeConstant C (2*A.mass))*∑ x∈F,nearOnePsi (9*C+4) (‖f x‖/level)) := by
  have h := positiveRestricted_to_truncated_modular A hC hR H F f hf hl
  intro D
  exact (h D).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun x _ _ => nearOnePsi_nonneg _ (div_nonneg (norm_nonneg _) hl.le)))
    (mul_nonneg hR (layerGaugeConstant_pos _ _).le))

theorem section7_modular_finite_card (A : PositiveAverageFamily) {C R : ℝ}
    (hC : 0≤C) (hR : 0≤R) (H : PositiveRestrictedGauge A C R)
    (F : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ x,x∉F → f x=0)
    {level : ℝ} (hl : 0<level) :
    {x | level<positiveMaximal A f x}.Finite ∧
      ({x | level<positiveMaximal A f x}.ncard : ℝ)≤
        (R*layerGaugeConstant C (2*A.mass))*∑ x∈F,nearOnePsi (9*C+4) (‖f x‖/level) := by
  have h := section7_modular_deduction A hC hR H F f hf hl
  exact ⟨testedDistribution_finite h,testedDistribution_ncard h⟩

end PrimeSquares
