import PrimeSquares.OriginalOrdinaryCollarMaximum

open scoped lp
namespace PrimeSquares

theorem circle_energy_maximal_witness (m : ℕ → C(PrimeCircle,ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ B^2) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (m j) f x‖) ∧
      (∀ x,0 ≤ g x) ∧ (∀ j x,‖integerMultiplier (m j) f x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖f‖ := by
  let F (j : ℕ) := integerMultiplier (m j) f
  have he := circleSymbols_operator_square_energy m hm
  have hf := operatorSquareEnergy_finite_bound (fun j => integerMultiplier (m j)) he f
  have hs : Summable (fun j => ‖F j‖^2) := finiteSquareEnergy_summable F hf
  refine ⟨squareMaximumL2 F hs,fun _ => rfl,?_,?_,?_⟩
  · exact squareMaximumValue_nonneg F hs
  · intro j x
    exact le_ciSup (squareMaximumValue_bddAbove F hs x) j
  · exact finiteSquareEnergy_maximal F (mul_nonneg hB (norm_nonneg _)) hf

end PrimeSquares
