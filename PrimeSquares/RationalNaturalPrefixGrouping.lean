import PrimeSquares.RationalDenominatorGrouping
open Finset
namespace PrimeSquares
theorem rational_natural_prefix_grouping {E : Type*} [AddCommMonoid E] (Γ : Finset ℚ) (M K : ℕ)
    (hΓ : ∀ r ∈ Γ,r.den ≤ M) (F : ℚ → E) :
    (∑ r ∈ Γ.filter (fun r => r.den ≤ K),F r)=
      ∑ q ∈ range (min (M+1) (K+1)),∑ r ∈ Γ.filter (fun r => r.den=q),F r := by
  classical
  have he : Γ.filter (fun r => r.den ∈ range (min (M+1) (K+1)))=Γ.filter (fun r => r.den ≤ K) := by
    ext r
    simp only [mem_filter,mem_range,lt_min_iff]
    constructor
    · intro h
      exact ⟨h.1,by omega⟩
    · intro h
      have hd := hΓ r h.1
      exact ⟨h.1,by omega⟩
  rw [←he]
  exact (sum_fiberwise_eq_sum_filter Γ (range (min (M+1) (K+1))) (fun r => r.den) F).symm
end PrimeSquares
