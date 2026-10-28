import PrimeSquares.RationalNaturalPrefixGrouping
open Finset
namespace PrimeSquares
theorem rational_real_prefix_grouping {E : Type*} [AddCommMonoid E] (Γ : Finset ℚ) (M : ℕ)
    (hΓ : ∀ r ∈ Γ,r.den ≤ M) {R : ℝ} (hR : 0 ≤ R) (F : ℚ → E) :
    (∑ r ∈ Γ.filter (fun r => (r.den : ℝ) ≤ R),F r)=
      ∑ q ∈ range (min (M+1) (⌊R⌋₊+1)),∑ r ∈ Γ.filter (fun r => r.den=q),F r := by
  have he (r : ℚ) : (r.den : ℝ) ≤ R ↔ r.den ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR).symm
  simp_rw [he]
  exact rational_natural_prefix_grouping Γ M ⌊R⌋₊ hΓ F
end PrimeSquares
