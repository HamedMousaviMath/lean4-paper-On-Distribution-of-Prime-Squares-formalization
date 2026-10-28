import PrimeSquares.KernelL1Value

open scoped lp
namespace PrimeSquares

noncomputable def kernelL1Operator (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) : ℓ¹(ℤ, ℂ) →L[ℂ] lp (fun _ : ℤ => ℂ) ⊤ :=
  LinearMap.mkContinuous
    { toFun := kernelL1Value K hK
      map_add' := kernelL1Value_add K hK
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext x
        change (∑' y, K (x-y)*(c • f) y) = c*(∑' y, K (x-y)*f y)
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        rw [← tsum_mul_left]
        apply tsum_congr
        intro y
        ring }
    B (kernelL1Value_norm K hK)

theorem kernelL1Operator_apply (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    kernelL1Operator K hK f x = ∑' y : ℤ, K (x-y)*f y := rfl

theorem kernelL1Operator_norm (K : ℤ → ℂ) {B : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ B) : ‖kernelL1Operator K hK‖ ≤ B :=
  (kernelL1Operator K hK).opNorm_le_bound ((norm_nonneg (K 0)).trans (hK 0))
    (kernelL1Value_norm K hK)

end PrimeSquares
