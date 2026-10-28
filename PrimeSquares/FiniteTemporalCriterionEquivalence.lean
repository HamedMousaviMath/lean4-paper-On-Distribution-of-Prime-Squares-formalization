import PrimeSquares.FiniteToCountableMaximum
open scoped lp
namespace PrimeSquares
theorem finiteTemporalMajorants_iff_countable (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ} (hB : 0 ≤ B) :
    FiniteTemporalMajorants F B ↔
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧ (∀ j x,‖F j x‖ ≤ g x) ∧ ‖g‖ ≤ B := by
  constructor
  · exact finite_to_countable_maximum F hB
  · rintro ⟨g,hg,ht,hn⟩ n
    exact ⟨g,hg,fun j _ => ht j,hn⟩
end PrimeSquares
