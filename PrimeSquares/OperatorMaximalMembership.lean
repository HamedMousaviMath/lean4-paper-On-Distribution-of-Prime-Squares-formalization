import PrimeSquares.CountableOperatorMaximum

open scoped lp
namespace PrimeSquares

theorem operatorMaximalValue_memLp
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Memℓp (operatorMaximalValue T f) 2 := by
  apply (countableOperatorEnvelope T f).2.mono
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (operatorMaximalValue_nonneg T hT f x)]
  exact operatorMaximalValue_le_envelope T hT f x

noncomputable def operatorMaximalL2
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨operatorMaximalValue T f,operatorMaximalValue_memLp T hT f⟩

theorem operatorMaximalL2_apply
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    operatorMaximalL2 T hT f x = ⨆ j : ℕ, ‖T j f x‖ := rfl

end PrimeSquares
