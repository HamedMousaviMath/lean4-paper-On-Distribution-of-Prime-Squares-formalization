import PrimeSquares.FiniteOperatorEnvelope

open Finset
open scoped lp
namespace PrimeSquares

theorem finiteOperatorEnvelope_norm {ι : Type*} (S : Finset ι)
    (T : ι → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (B : ι → ℝ)
    (hT : ∀ i ∈ S, ‖T i‖ ≤ B i) (f : ℓ²(ℤ, ℂ)) :
    ‖finiteOperatorEnvelope S T f‖ ≤ (∑ i ∈ S, B i)*‖f‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖magnitudeL2 (T i f)‖ := norm_sum_le _ _
    _ = ∑ i ∈ S, ‖T i f‖ := by simp only [magnitudeL2_norm]
    _ ≤ ∑ i ∈ S, B i*‖f‖ := sum_le_sum (fun i hi =>
      ((T i).le_opNorm f).trans (mul_le_mul_of_nonneg_right (hT i hi) (norm_nonneg _)))
    _ = _ := (sum_mul ..).symm

theorem finiteOperator_dominated_maximal {ι : Type*} (S : Finset ι)
    (T : ι → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (B : ι → ℝ)
    (hT : ∀ i ∈ S, ‖T i‖ ≤ B i) (f : ℓ²(ℤ, ℂ)) (M : ℤ → ℝ)
    (hM0 : ∀ x, 0 ≤ M x) (hM : ∀ x, M x ≤ finiteOperatorEnvelope S T f x) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2, (∀ x, g x = M x) ∧
      ‖g‖ ≤ (∑ i ∈ S, B i)*‖f‖ := by
  have hm : Memℓp M 2 := (finiteOperatorEnvelope S T f).2.mono (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hM0 x)]
    exact hM x)
  refine ⟨⟨M,hm⟩,fun _ => rfl,?_⟩
  apply le_trans _ (finiteOperatorEnvelope_norm S T B hT f)
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change ‖M x‖ ≤ ‖finiteOperatorEnvelope S T f x‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hM0 x),
    abs_of_nonneg (finiteOperatorEnvelope_nonneg S T f x)]
  exact hM x

end PrimeSquares
