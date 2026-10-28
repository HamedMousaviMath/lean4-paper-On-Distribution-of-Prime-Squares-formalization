import PrimeSquares.FiniteFamilyCountableCriterion
import PrimeSquares.CircleMultipliers
open scoped lp
namespace PrimeSquares
theorem finite_multiplier_countable_maximum (m : ℕ → C(PrimeCircle,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ J : Finset ℕ,∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j ∈ J,∀ x,‖integerMultiplier (m j) f x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖f‖)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (m j) f x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖f‖ :=
  finite_family_countable_maximum _ (mul_nonneg hB (norm_nonneg _)) (fun J => hF J f)
end PrimeSquares
