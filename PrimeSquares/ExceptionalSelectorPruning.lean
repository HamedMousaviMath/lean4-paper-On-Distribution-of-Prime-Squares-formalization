import PrimeSquares.SourceEffectiveConductorFilter
open Finset
namespace PrimeSquares
theorem rationalCollarBlock_exceptional_prune (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (W : ℝ) (β : ℚ → ℝ) (q₀ : ℕ) (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) :
    rationalCollarBlock Γ N hN W β (fun r => sourceExceptionalSelector q₀ active r*rationalTwistedGauss r (χ r))=
      rationalCollarBlock (Γ.filter (fun r => q₀ ∣ r.den)) N hN W β
        (fun r => sourceExceptionalSelector q₀ active r*rationalTwistedGauss r (χ r)) := by
  classical
  rw [rationalCollarBlock_filter]
  unfold rationalCollarBlock
  apply sum_congr rfl
  intro r _
  by_cases hd : q₀ ∣ r.den <;> simp [sourceExceptionalSelector,hd]
end PrimeSquares
