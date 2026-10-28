import PrimeSquares.KernelL1Operator

open scoped lp
namespace PrimeSquares

noncomputable def operatorL1MaxValue
    (T : ℕ → ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) : ℝ :=
  ⨆ j : ℕ,‖T j f x‖

theorem operatorL1MaxValue_bdd
    (T : ℕ → ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤) {B : ℝ}
    (hT : ∀ j : ℕ,‖T j‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    BddAbove (Set.range (fun j : ℕ => ‖T j f x‖)) := by
  refine ⟨B*‖f‖,?_⟩
  rintro _ ⟨j,rfl⟩
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (T j f) x).trans
    ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg _)))

theorem operatorL1MaxValue_nonneg
    (T : ℕ → ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤) {B : ℝ}
    (hT : ∀ j : ℕ,‖T j‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) : 0 ≤ operatorL1MaxValue T f x :=
  (norm_nonneg (T 0 f x)).trans (le_ciSup (operatorL1MaxValue_bdd T hT f x) 0)

theorem operatorL1MaxValue_bound
    (T : ℕ → ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤) {B : ℝ}
    (hT : ∀ j : ℕ,‖T j‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    operatorL1MaxValue T f x ≤ B*‖f‖ := by
  apply ciSup_le
  intro j
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (T j f) x).trans
    ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hT j) (norm_nonneg _)))

noncomputable def operatorL1Maximum
    (T : ℕ → ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤) {B : ℝ}
    (hT : ∀ j : ℕ,‖T j‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) : lp (fun _ : ℤ => ℝ) ⊤ :=
  ⟨operatorL1MaxValue T f,memℓp_infty ⟨B*‖f‖,by
    rintro _ ⟨x,rfl⟩
    change ‖operatorL1MaxValue T f x‖ ≤ B*‖f‖
    rw [Real.norm_eq_abs,abs_of_nonneg (operatorL1MaxValue_nonneg T hT f x)]
    exact operatorL1MaxValue_bound T hT f x⟩⟩

theorem operatorL1Maximum_norm
    (T : ℕ → ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤) {B : ℝ}
    (hT : ∀ j : ℕ,‖T j‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) :
    ‖operatorL1Maximum T hT f‖ ≤ B*‖f‖ := by
  apply lp.norm_le_of_forall_le'
  intro x
  change ‖operatorL1MaxValue T f x‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (operatorL1MaxValue_nonneg T hT f x)]
  exact operatorL1MaxValue_bound T hT f x

end PrimeSquares
