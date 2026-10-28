import PrimeSquares.ChangingSourceCollarPairing
open Finset
namespace PrimeSquares
noncomputable def denominatorActivation (R : ℝ) (q : ℕ) : ℂ := if (q : ℝ) ≤ R then 1 else 0
theorem denominator_activation_sum (Γ : Finset ℚ) (R : ℝ) (v : ℚ → ℂ) :
    (∑ r ∈ Γ.filter (fun r => (r.den : ℝ) ≤ R),v r)=∑ r ∈ Γ,denominatorActivation R r.den*v r := by
  classical
  rw [sum_filter]
  apply sum_congr rfl
  intro r _
  by_cases h : (r.den : ℝ) ≤ R <;> simp [denominatorActivation,h]
theorem denominatorActivation_norm (R : ℝ) (q : ℕ) : ‖denominatorActivation R q‖ ≤ 1 := by
  unfold denominatorActivation
  split_ifs <;> norm_num
end PrimeSquares
