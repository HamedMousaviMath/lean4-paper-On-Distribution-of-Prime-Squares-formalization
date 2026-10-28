import PrimeSquares.OperatorDecaySeries
import PrimeSquares.OperatorMaximalNorm

open scoped lp
namespace PrimeSquares

theorem decaying_operator_maximal_tail {K s : ℝ} (hK : 0 ≤ K) (hs : 2 ≤ s) (J : ℕ)
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ j : ℕ, ‖T (J+j)‖ ≤ K*((J+j : ℕ)+1 : ℝ)^(-s)) (f : ℓ²(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, g x = ⨆ j : ℕ, ‖T (J+j) f x‖) ∧
      ‖g‖ ≤ 2*K*((J : ℝ)+1)^(1-s)*‖f‖ := by
  have hsum := operator_norm_shift_summable hK hs J T hT
  refine ⟨operatorMaximalL2 (fun j => T (J+j)) hsum f,fun x => rfl,?_⟩
  exact (operatorMaximalL2_norm_bound _ hsum f).trans
    (mul_le_mul_of_nonneg_right (operator_norm_shift_tsum_bound hK hs J T hT) (norm_nonneg f))

theorem decaying_operator_maximal_tail_majorant {K s : ℝ} (hK : 0 ≤ K) (hs : 2 ≤ s) (J : ℕ)
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : ∀ j : ℕ, ‖T (J+j)‖ ≤ K*((J+j : ℕ)+1 : ℝ)^(-s)) (f : ℓ²(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,
      (∀ x : ℤ, 0 ≤ g x) ∧ (∀ (j : ℕ) (x : ℤ), ‖T (J+j) f x‖ ≤ g x) ∧
      ‖g‖ ≤ 2*K*((J : ℝ)+1)^(1-s)*‖f‖ := by
  have hsum := operator_norm_shift_summable hK hs J T hT
  refine ⟨countableOperatorEnvelope (fun j => T (J+j)) f,
    countableOperatorEnvelope_nonneg _ hsum f,?_,?_⟩
  · exact fun j x => countableOperatorEnvelope_dominates _ hsum f j x
  · exact (countableOperatorEnvelope_norm _ hsum f).trans
      (mul_le_mul_of_nonneg_right (operator_norm_shift_tsum_bound hK hs J T hT) (norm_nonneg f))

end PrimeSquares
