import PrimeSquares.DyadicActualLowData

open scoped lp
namespace PrimeSquares

theorem dyadicActualLow_countable_maximum {M : ℕ} (hM : 2 ≤ M) {Q : ℝ} (hQ : 2 ≤ Q)
    (hbudget : ∀ j : ℕ,(sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q)^4 ≤ ((((2 : ℕ)^j*M : ℕ) : ℝ))/2)
    (q₀ : ℕ → ℕ) (hq₀ : ∀ j,0 < q₀ j) (χ : ∀ j,DirichletCharacter ℂ (q₀ j)) (hχ : ∀ j,(χ j).IsQuadratic)
    (active : ℕ → Bool) (β : ℕ → ℝ) (hβ : ∀ j,β j ≤ 1) (f : ℓ¹(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
      (∀ x,g x=⨆ j : ℕ,‖integerMultiplier (dyadicActualLowData hM hQ hbudget q₀ hq₀ χ hχ active β hβ j).symbol
        (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖) ∧
      ‖g‖ ≤ 2*realLowAmplitude M Q*‖f‖ := by
  apply naturalSourceLow_countable_maximal hM (fun j => (2 : ℕ)^j*M)
    (dyadicActualLowData hM hQ hbudget q₀ hq₀ χ hχ active β hβ) _ f
  intro j
  have hp : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by norm_num)
  simpa only [one_mul] using Nat.mul_le_mul_right M hp

end PrimeSquares
