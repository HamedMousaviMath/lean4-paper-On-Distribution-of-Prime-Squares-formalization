import PrimeSquares.CountableOperatorEnvelope

open scoped lp
namespace PrimeSquares

theorem countableOperatorEnvelope_coordinate
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    countableOperatorEnvelope T f x = ∑' j : ℕ, ‖T j f x‖ := by
  exact (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 x).map_tsum (operator_magnitude_summable T hT f)

theorem operator_coordinate_norm_summable
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    Summable (fun j : ℕ => ‖T j f x‖) := by
  exact (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 x).summable (operator_magnitude_summable T hT f)

theorem countableOperatorEnvelope_coordinate_bound
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    |countableOperatorEnvelope T f x| ≤ (∑' j : ℕ, ‖T j‖)*‖f‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (countableOperatorEnvelope T f) x
  have ha : |countableOperatorEnvelope T f x| ≤ ‖countableOperatorEnvelope T f‖ := by
    simpa only [Real.norm_eq_abs] using h
  exact ha.trans (countableOperatorEnvelope_norm T hT f)

end PrimeSquares
