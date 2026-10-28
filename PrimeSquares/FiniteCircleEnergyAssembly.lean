import PrimeSquares.FiniteSquareEnergyAssembly

open Finset
open scoped lp
namespace PrimeSquares

theorem finite_circle_energy_assemble {ι : Type*} (S : Finset ι) (m : ℕ → ι → C(PrimeCircle,ℂ))
    (B : ι → ℝ) (hB : ∀ i ∈ S,0 < B i)
    (hE : ∀ i ∈ S,∀ J : Finset ℕ,∀ θ,(∑ j ∈ J,‖m j i θ‖^2) ≤ (B i)^2) :
    ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖(∑ i ∈ S,m j i) θ‖^2) ≤ (∑ i ∈ S,B i)^2 := by
  intro J θ
  simp only [ContinuousMap.sum_apply]
  exact finite_square_energy_assemble S J (fun j i => m j i θ) B hB (fun i hi => hE i hi J θ)

theorem finite_circle_countable_maximum {ι : Type*} (S : Finset ι) (m : ℕ → ι → C(PrimeCircle,ℂ))
    (B : ι → ℝ) (hB : ∀ i ∈ S,0 < B i)
    (hE : ∀ i ∈ S,∀ J : Finset ℕ,∀ θ,(∑ j ∈ J,‖m j i θ‖^2) ≤ (B i)^2) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (∑ i ∈ S,m j i) f x‖) ∧ ‖g‖ ≤ (∑ i ∈ S,B i)*‖f‖ :=
  circle_symbol_countable_maximal _ (sum_nonneg (fun i hi => (hB i hi).le))
    (finite_circle_energy_assemble S m B hB hE) f

end PrimeSquares
