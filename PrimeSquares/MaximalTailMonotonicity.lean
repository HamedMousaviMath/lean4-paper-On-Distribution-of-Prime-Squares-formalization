import PrimeSquares.OperatorMaximalNorm

open scoped lp
namespace PrimeSquares

theorem operator_tail_norm_summable
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (J : ℕ) :
    Summable (fun j : ℕ => ‖T (J+j)‖) := hT.comp_injective (add_right_injective J)

theorem operatorMaximalValue_tail_mono
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) {J K : ℕ} (hJK : J ≤ K)
    (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    operatorMaximalValue (fun j => T (K+j)) f x ≤ operatorMaximalValue (fun j => T (J+j)) f x := by
  apply ciSup_le
  intro j
  have he : K+j = J+(K-J+j) := by omega
  have hd := operatorMaximalValue_dominates (fun m => T (J+m)) (operator_tail_norm_summable T hT J) f (K-J+j) x
  have hl : ‖T (K+j) f x‖ = ‖T (J+(K-J+j)) f x‖ := congrArg (fun n : ℕ => ‖T n f x‖) he
  exact hl.trans_le hd

theorem operatorMaximalL2_tail_mono
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) {J K : ℕ} (hJK : J ≤ K) (f : ℓ²(ℤ, ℂ)) :
    ‖operatorMaximalL2 (fun j => T (K+j)) (operator_tail_norm_summable T hT K) f‖ ≤
      ‖operatorMaximalL2 (fun j => T (J+j)) (operator_tail_norm_summable T hT J) f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change ‖operatorMaximalValue (fun j => T (K+j)) f x‖ ≤ ‖operatorMaximalValue (fun j => T (J+j)) f x‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (operatorMaximalValue_nonneg _ (operator_tail_norm_summable T hT K) f x),
    abs_of_nonneg (operatorMaximalValue_nonneg _ (operator_tail_norm_summable T hT J) f x)]
  exact operatorMaximalValue_tail_mono T hT hJK f x

end PrimeSquares
