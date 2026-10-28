import PrimeSquares.FiniteTemporalMajorants
open scoped lp
namespace PrimeSquares
theorem initialTemporalMaximum_mem_l2 (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ}
    (hF : FiniteTemporalMajorants F B) (n : ℕ) : Memℓp (initialTemporalMaximum F n) 2 := by
  obtain ⟨g,_,hg,_⟩ := hF n
  apply g.2.mono
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (initialTemporalMaximum_nonneg F n x)]
  exact partialSups_le _ n _ (fun j hj => hg j hj x)
noncomputable def initialTemporalMaximumL2 (F : ℕ → ℓ²(ℤ,ℂ)) {B : ℝ}
    (hF : FiniteTemporalMajorants F B) (n : ℕ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨initialTemporalMaximum F n,initialTemporalMaximum_mem_l2 F hF n⟩
end PrimeSquares
