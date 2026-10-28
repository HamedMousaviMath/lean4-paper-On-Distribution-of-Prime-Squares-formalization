import PrimeSquares.OperatorMaximalNorm

open scoped lp
namespace PrimeSquares

theorem operatorMaximalValue_add
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f g : ℓ²(ℤ, ℂ)) (x : ℤ) :
    operatorMaximalValue T (f+g) x ≤ operatorMaximalValue T f x+operatorMaximalValue T g x := by
  apply ciSup_le
  intro j
  calc
    _ = ‖T j f x+T j g x‖ := by rw [map_add];rfl
    _ ≤ ‖T j f x‖+‖T j g x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (operatorMaximalValue_dominates T hT f j x)
      (operatorMaximalValue_dominates T hT g j x)

theorem operatorMaximalValue_neg
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    operatorMaximalValue T (-f) x = operatorMaximalValue T f x := by
  unfold operatorMaximalValue
  congr 1
  funext j
  rw [map_neg]
  change ‖-T j f x‖ = _
  exact norm_neg _

theorem operatorMaximalValue_smul_le
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (z : ℂ) (x : ℤ) :
    operatorMaximalValue T (z • f) x ≤ ‖z‖*operatorMaximalValue T f x := by
  apply ciSup_le
  intro j
  calc
    _ = ‖z * T j f x‖ := by rw [map_smul];rfl
    _ = ‖z‖*‖T j f x‖ := norm_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (operatorMaximalValue_dominates T hT f j x) (norm_nonneg z)

end PrimeSquares
