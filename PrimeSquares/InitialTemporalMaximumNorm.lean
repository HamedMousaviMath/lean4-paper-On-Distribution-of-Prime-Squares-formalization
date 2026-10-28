import PrimeSquares.InitialTemporalMaximumL2
open scoped lp
namespace PrimeSquares
theorem initialTemporalMaximumL2_norm (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ}
    (hF : FiniteTemporalMajorants F B) (n : ℕ) : ‖initialTemporalMaximumL2 F hF n‖ ≤ B := by
  obtain ⟨g,hg0,hg,hn⟩ := hF n
  apply le_trans _ hn
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change ‖initialTemporalMaximum F n x‖ ≤ ‖g x‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (initialTemporalMaximum_nonneg F n x),
    abs_of_nonneg (hg0 x)]
  exact partialSups_le _ n _ (fun j hj => hg j hj x)
end PrimeSquares
