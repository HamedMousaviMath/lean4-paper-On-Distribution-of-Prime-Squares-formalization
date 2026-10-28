import PrimeSquares.DyadicSparseSum

open Finset
namespace PrimeSquares

theorem rational_dyadic_partition {A : Type*} [AddCommMonoid A] (Γ : Finset ℚ) (M : ℕ)
    (hden : ∀ r ∈ Γ,r.den ≤ M) (F : ℚ → A) :
    (∑ r ∈ Γ,F r)=∑ s ∈ range (Nat.log2 M+1),∑ r ∈ Γ.filter (fun r => Nat.log2 r.den=s),F r := by
  classical
  symm
  apply sum_fiberwise_of_maps_to
  intro r hr
  have hd := hden r hr
  have hMp : M ≠ 0 := by have hp := r.den_pos;omega
  have hl : Nat.log2 r.den ≤ Nat.log2 M :=
    (Nat.le_log2 hMp).mpr ((Nat.log2_self_le r.den_pos.ne').trans hd)
  exact mem_range.mpr (by omega)

end PrimeSquares
