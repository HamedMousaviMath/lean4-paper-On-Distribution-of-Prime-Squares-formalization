import PrimeSquares.InitialTemporalMaximum
open scoped lp
namespace PrimeSquares
def FiniteTemporalMajorants (F : ℕ → ℓ²(ℤ,ℂ)) (B : ℝ) : Prop :=
  ∀ n : ℕ,∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
    (∀ j,j ≤ n → ∀ x,‖F j x‖ ≤ g x) ∧ ‖g‖ ≤ B
theorem finiteTemporalMajorants_coordinate_bound (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ}
    (hF : FiniteTemporalMajorants F B) (j : ℕ) (x : ℤ) : ‖F j x‖ ≤ B := by
  obtain ⟨g,_,hg,hn⟩ := hF j
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) g x
  have ha : g x ≤ ‖g x‖ := le_abs_self _
  exact (hg j le_rfl x).trans (ha.trans (he.trans hn))
end PrimeSquares
