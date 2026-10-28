import PrimeSquares.KernelL1Summation

open scoped lp
namespace PrimeSquares

noncomputable def kernelL1Value (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) : lp (fun _ : ℤ => ℂ) ⊤ :=
  ⟨kernelL1Sum K f, memℓp_infty ⟨B*‖f‖, by
    rintro _ ⟨x,rfl⟩
    exact kernelL1Sum_bound K hK f x⟩⟩

theorem kernelL1Value_norm (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) :
    ‖kernelL1Value K hK f‖ ≤ B*‖f‖ :=
  lp.norm_le_of_forall_le' _ (kernelL1Sum_bound K hK f)

theorem kernelL1Value_add (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (f g : ℓ¹(ℤ, ℂ)) :
    kernelL1Value K hK (f+g) = kernelL1Value K hK f + kernelL1Value K hK g := by
  apply Subtype.ext
  funext x
  change (∑' y, K (x-y)*(f+g) y) = (∑' y, K (x-y)*f y)+(∑' y, K (x-y)*g y)
  simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  exact (kernelL1_summable K hK f x).tsum_add (kernelL1_summable K hK g x)

end PrimeSquares
