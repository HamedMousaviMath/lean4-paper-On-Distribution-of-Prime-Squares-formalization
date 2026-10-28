import PrimeSquares.CircleSymbolSquareEnergy

open scoped lp
namespace PrimeSquares

theorem circle_symbol_countable_maximal (m : ℕ → C(PrimeCircle, ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ B^2) (f : ℓ²(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖integerMultiplier (m j) f x‖) ∧ ‖g‖ ≤ B*‖f‖ :=
  operatorSquareEnergy_countable_maximal _ hB (circleSymbols_operator_square_energy m hm) f

theorem circle_symbol_attenuated_maximal (m n : ℕ → C(PrimeCircle, ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ j ∈ J,‖m j θ‖^2) ≤ B^2)
    (hn : ∀ j : ℕ,∀ θ : PrimeCircle,‖n j θ‖ ≤ ‖m j θ‖) (f : ℓ²(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖integerMultiplier (n j) f x‖) ∧ ‖g‖ ≤ B*‖f‖ := by
  apply circle_symbol_countable_maximal n hB _ f
  intro J θ
  exact (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hn j θ) 2)).trans (hm J θ)

end PrimeSquares
