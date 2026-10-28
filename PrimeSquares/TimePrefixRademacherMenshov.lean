import PrimeSquares.BinaryNodeUniformBudget
open scoped lp
namespace PrimeSquares
theorem time_prefix_rademacherMenshov (h a : ℕ) (u : ℕ → ℕ → ℤ → ℂ)
    (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) (w : ℕ → ℝ) (hw : ∀ i,0 ≤ w i)
    {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t k b x,‖intervalComplexSum b (2^k) (fun i => u t i x)‖ ≤ G k b x)
    (hI : ∀ k b,‖G k b‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t K,K ≤ 2^h → ∀ x,‖intervalComplexSum a K (fun i => u t i x)‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h) w) := by
  refine ⟨timePrefixL2Majorant h a G,timePrefixL2Majorant_nonneg h a G,
    fun t K hK x => time_prefix_pointwise_envelope h a K hK u G hG t x,?_⟩
  rw [timePrefixL2Majorant_norm]
  have hn := intervalRealBudget_nonneg a (2^h) w hw
  have he := binaryNode_uniform_budget h a G w B hI
  have hh : (h+1 : ℝ)*B^2*intervalRealBudget a (2^h) w=
      (Real.sqrt (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h) w))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hn]
  rw [hh] at he
  have ht := Real.sqrt_le_sqrt he
  rw [Real.sqrt_sq (by positivity)] at ht
  calc
    _ ≤ Real.sqrt (h+1 : ℝ)*(Real.sqrt (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h) w)) :=
      mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
    _ = _ := by rw [←mul_assoc,←mul_assoc,Real.mul_self_sqrt (by positivity)]
end PrimeSquares
