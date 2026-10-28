import PrimeSquares.RealCutoffScalarPrefix
open Finset
namespace PrimeSquares
theorem rational_denominator_grouping {E : Type*} [AddCommMonoid E] (Γ : Finset ℚ) (M : ℕ)
    (hΓ : ∀ r ∈ Γ,r.den ≤ M) (F : ℚ → E) :
    (∑ r ∈ Γ,F r)=∑ q ∈ range (M+1),∑ r ∈ Γ.filter (fun r => r.den=q),F r := by
  exact (sum_fiberwise_of_maps_to (fun r hr => mem_range.mpr (Nat.lt_succ_of_le (hΓ r hr))) F).symm
end PrimeSquares
