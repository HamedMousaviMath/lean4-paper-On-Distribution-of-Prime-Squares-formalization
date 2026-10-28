import PrimeSquares.FiniteSquareEnergy

open scoped lp
namespace PrimeSquares

def OperatorSquareEnergyBound (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (B : ℝ) : Prop :=
  ∀ f : ℓ²(ℤ, ℂ),∀ S : Finset ℕ,(∑ j ∈ S,‖T j f‖^2) ≤ B^2*‖f‖^2

theorem operatorSquareEnergy_finite_bound (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    {B : ℝ} (hT : OperatorSquareEnergyBound T B) (f : ℓ²(ℤ, ℂ)) :
    FiniteSquareEnergyBound (fun j => T j f) (B*‖f‖) := by
  intro S
  simpa only [mul_pow] using hT f S

theorem operatorSquareEnergy_countable_maximal (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    {B : ℝ} (hB : 0 ≤ B) (hT : OperatorSquareEnergyBound T B) (f : ℓ²(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖T j f x‖) ∧ ‖g‖ ≤ B*‖f‖ := by
  let hF := operatorSquareEnergy_finite_bound T hT f
  exact ⟨squareMaximumL2 (fun j => T j f) (finiteSquareEnergy_summable _ hF),fun _ => rfl,
    finiteSquareEnergy_maximal _ (mul_nonneg hB (norm_nonneg _)) hF⟩

end PrimeSquares
