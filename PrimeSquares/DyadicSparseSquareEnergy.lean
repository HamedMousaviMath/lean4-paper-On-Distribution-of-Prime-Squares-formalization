import PrimeSquares.FiniteSumSquareCardinality
import PrimeSquares.DyadicSparseSum

open Finset
namespace PrimeSquares

theorem dyadic_sparse_square_energy (Γ : Finset ℚ) (ξ : ℝ) (s : ℕ) (J : Finset ℕ)
    (F : ℕ → ℚ → ℂ) (A : ℝ) (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    (hz : ∀ j ∈ J,∀ r ∈ Γ,sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))=0 → F j r=0)
    (hE : ∀ r ∈ Γ,(∑ j ∈ J,‖F j r‖^2) ≤ A^2) :
    (∑ j ∈ J,‖∑ r ∈ Γ,F j r‖^2) ≤ (4*A)^2 := by
  classical
  let S := activeRationalCenters Γ ξ
  have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast dyadicActive_card Γ ξ s hΓ hlog
  have hrewrite (j : ℕ) (hj : j ∈ J) : (∑ r ∈ Γ,F j r)=∑ r ∈ S,F j r :=
    rational_sum_eq_active Γ ξ (F j) (hz j hj)
  calc
    _ = ∑ j ∈ J,‖∑ r ∈ S,F j r‖^2 := sum_congr rfl (fun j hj => by rw [hrewrite j hj])
    _ ≤ ∑ j ∈ J,4*(∑ r ∈ S,‖F j r‖^2) := by
      apply sum_le_sum
      intro j _
      exact (norm_finset_sum_square_card S (F j)).trans (mul_le_mul_of_nonneg_right hc (sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = 4*(∑ r ∈ S,∑ j ∈ J,‖F j r‖^2) := by rw [←mul_sum,sum_comm]
    _ ≤ 4*(∑ _ ∈ S,A^2) := mul_le_mul_of_nonneg_left (sum_le_sum (fun r hr => hE r (mem_filter.mp hr).1)) (by norm_num)
    _ ≤ (4*A)^2 := by
      simp only [sum_const,nsmul_eq_mul]
      have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg A)
      nlinarith

end PrimeSquares
