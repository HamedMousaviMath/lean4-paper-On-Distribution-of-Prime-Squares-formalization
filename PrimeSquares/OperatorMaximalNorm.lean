import PrimeSquares.OperatorMaximalMembership

open scoped lp
namespace PrimeSquares

theorem operatorMaximalL2_norm_le_envelope
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    ‖operatorMaximalL2 T hT f‖ ≤ ‖countableOperatorEnvelope T f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change ‖operatorMaximalValue T f x‖ ≤ ‖countableOperatorEnvelope T f x‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (operatorMaximalValue_nonneg T hT f x),
    abs_of_nonneg (countableOperatorEnvelope_nonneg T hT f x)]
  exact operatorMaximalValue_le_envelope T hT f x

theorem operatorMaximalL2_norm_bound
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    ‖operatorMaximalL2 T hT f‖ ≤ (∑' j : ℕ, ‖T j‖)*‖f‖ :=
  (operatorMaximalL2_norm_le_envelope T hT f).trans (countableOperatorEnvelope_norm T hT f)

end PrimeSquares
