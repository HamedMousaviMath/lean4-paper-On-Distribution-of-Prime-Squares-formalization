import PrimeSquares.DyadicActiveBound

open Finset
namespace PrimeSquares

theorem rational_sum_eq_active (Γ : Finset ℚ) (ξ : ℝ) (F : ℚ → ℂ)
    (hzero : ∀ r ∈ Γ,sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))=0 → F r=0) :
    (∑ r ∈ Γ,F r)=∑ r ∈ activeRationalCenters Γ ξ,F r := by
  classical
  symm
  rw [activeRationalCenters,sum_filter]
  apply sum_congr rfl
  intro r hr
  by_cases hp : sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) ≠ 0
  · rw [ite_eq_left hp]
  · rw [ite_eq_right hp,hzero r hr (not_not.mp hp)]

theorem dyadic_sparse_sum_bound (Γ : Finset ℚ) (ξ : ℝ) (s : ℕ) (F : ℚ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    (hzero : ∀ r ∈ Γ,sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))=0 → F r=0)
    (hF : ∀ r ∈ Γ,‖F r‖ ≤ B) : ‖∑ r ∈ Γ,F r‖ ≤ 4*B := by
  classical
  rw [rational_sum_eq_active Γ ξ F hzero]
  calc
    _ ≤ ∑ r ∈ activeRationalCenters Γ ξ,‖F r‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ activeRationalCenters Γ ξ,B := sum_le_sum (fun r hr => hF r (mem_filter.mp hr).1)
    _ ≤ 4*B := by
      have hc : ((activeRationalCenters Γ ξ).card : ℝ) ≤ 4 := by exact_mod_cast dyadicActive_card Γ ξ s hΓ hlog
      simpa using mul_le_mul_of_nonneg_right hc hB

end PrimeSquares
