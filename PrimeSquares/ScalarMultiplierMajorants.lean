import PrimeSquares.CircleMultipliers
open scoped lp
namespace PrimeSquares
theorem scalar_multiplier_majorant (m : ℕ→C(PrimeCircle,ℂ)) (c : ℕ→ℂ)
    {A B : ℝ} (hA : 0≤A) (hc : ∀ j,‖c j‖≤A) (f : ℓ²(ℤ,ℂ))
    (g : lp (fun _ : ℤ=>ℝ) 2) (hg : ∀ x,0≤g x)
    (ht : ∀ j x,‖integerMultiplier (m j) f x‖≤g x) (hn : ‖g‖≤B*‖f‖) :
    ∃ u : lp (fun _ : ℤ=>ℝ) 2,(∀ x,0≤u x) ∧
      (∀ j x,‖integerMultiplier (c j • m j) f x‖≤u x) ∧ ‖u‖≤(A*B)*‖f‖ := by
  refine ⟨A • g,fun x=>by simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] using mul_nonneg hA (hg x),?_,?_⟩
  · intro j x
    rw [integerMultiplier_smul]
    change ‖c j • integerMultiplier (m j) f x‖≤A*g x
    rw [norm_smul]
    exact mul_le_mul (hc j) (ht j x) (norm_nonneg _) hA
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hA]
    exact (mul_le_mul_of_nonneg_left hn hA).trans_eq (by ring)
end PrimeSquares
