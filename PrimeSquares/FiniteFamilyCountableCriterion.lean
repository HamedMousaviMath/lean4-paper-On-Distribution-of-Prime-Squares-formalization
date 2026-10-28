import PrimeSquares.FiniteToCountableMaximum
open Finset
open scoped lp
namespace PrimeSquares
theorem finite_family_countable_maximum (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ J : Finset ℕ,∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j ∈ J,∀ x,‖F j x‖ ≤ g x) ∧ ‖g‖ ≤ B) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧ (∀ j x,‖F j x‖ ≤ g x) ∧ ‖g‖ ≤ B := by
  apply finite_to_countable_maximum F hB
  intro n
  obtain ⟨g,hg,ht,hn⟩ := hF (range (n+1))
  exact ⟨g,hg,fun j hj => ht j (mem_range.mpr (by omega)),hn⟩
end PrimeSquares
