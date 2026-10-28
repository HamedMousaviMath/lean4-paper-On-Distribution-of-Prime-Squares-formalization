import PrimeSquares.CollarBroadSupport

open Finset
namespace PrimeSquares

theorem annularCollarSymbol_finite_energy {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q)
    (s : ℕ) (J : Finset ℕ) (θ : ℝ) :
    (∑ j ∈ J,‖annularCollarSymbol ((2 : ℕ)^j*M) (by have hh := dyadic_annular_scale_lower hM j;omega) (β j) q Q s θ‖^2) ≤
      (8*q/(Real.pi*Q))^2 := by
  calc
    _ ≤ ∑ j ∈ J,‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2 := by
      apply sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (annularCollarSymbol_le_factor _ _ _ _ _ _ _) 2
    _ ≤ _ := collarFactor_finite_square_simple hM β hβ0 hβ1 hq hQ J θ

end PrimeSquares
