import PrimeSquares.WeightedSmoothSourceFactorization
import PrimeSquares.IntegerMultiplierComposition
open Finset
open scoped lp
namespace PrimeSquares
theorem weightedSmoothSource_operator {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (c : ℚ → ℂ) (ha : 1 ≤ (N : ℝ)^2) (hscale : (16 : ℝ)^s ≤ (N : ℝ)^2) (f : ℓ²(ℤ,ℂ)) :
    integerMultiplier (∑ r ∈ Γ,c r • circleAnnularSmoothProjection N s r) f=
      integerMultiplier (∑ t ∈ Γ,circleSmoothCutoff ((N : ℝ)^2) ha t)
        (integerMultiplier (weightedSourceCutoff Γ s c) f) := by
  rw [integerMultiplier_comp_apply,mul_comm,
    weightedSmoothSource_factorization hN hs Γ hc hd c ha hscale]
end PrimeSquares
