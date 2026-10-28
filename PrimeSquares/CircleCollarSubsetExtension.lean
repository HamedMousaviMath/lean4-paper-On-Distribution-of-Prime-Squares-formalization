import PrimeSquares.RationalCollarFilter
open Finset
namespace PrimeSquares
theorem rationalCollarBlock_subset (Γ Λ : Finset ℚ) (hsub : Λ ⊆ Γ)
    (N : ℕ) (hN : 1 ≤ N) (W : ℝ) (β : ℚ → ℝ) (c : ℚ → ℂ) :
    rationalCollarBlock Λ N hN W β c=
      rationalCollarBlock Γ N hN W β (fun r => if r ∈ Λ then c r else 0) := by
  classical
  have hf : Γ.filter (fun r => r ∈ Λ)=Λ := by
    ext r
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
  rw [←rationalCollarBlock_filter, hf]
end PrimeSquares
