import PrimeSquares.OperatorMaximalSublinearity

open scoped lp
namespace PrimeSquares

theorem operatorMaximalValue_difference_bound
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f g : ℓ²(ℤ, ℂ)) (x : ℤ) :
    |operatorMaximalValue T f x-operatorMaximalValue T g x| ≤ operatorMaximalValue T (f-g) x := by
  have h₁ := operatorMaximalValue_add T hT (f-g) g x
  rw [sub_add_cancel] at h₁
  have h₂ := operatorMaximalValue_add T hT (g-f) f x
  rw [sub_add_cancel] at h₂
  have he : g-f = -(f-g) := by abel
  rw [he,operatorMaximalValue_neg] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem operatorMaximalL2_difference_bound
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f g : ℓ²(ℤ, ℂ)) :
    ‖operatorMaximalL2 T hT f-operatorMaximalL2 T hT g‖ ≤ (∑' j : ℕ, ‖T j‖)*‖f-g‖ := by
  have hm : ‖operatorMaximalL2 T hT f-operatorMaximalL2 T hT g‖ ≤ ‖operatorMaximalL2 T hT (f-g)‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro x
    change ‖operatorMaximalValue T f x-operatorMaximalValue T g x‖ ≤ ‖operatorMaximalValue T (f-g) x‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (operatorMaximalValue_nonneg T hT (f-g) x)]
    exact operatorMaximalValue_difference_bound T hT f g x
  exact hm.trans (operatorMaximalL2_norm_bound T hT (f-g))

theorem operatorMaximalL2_lipschitz
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) :
    LipschitzWith (NNReal.mk (∑' j : ℕ, ‖T j‖) (tsum_nonneg (fun j => norm_nonneg (T j)))) (operatorMaximalL2 T hT) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [dist_eq_norm,NNReal.coe_mk] using operatorMaximalL2_difference_bound T hT f g

end PrimeSquares
