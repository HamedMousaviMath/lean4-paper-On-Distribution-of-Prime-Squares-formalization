import PrimeSquares.BinaryTreeUniformBudget
open scoped lp
namespace PrimeSquares
theorem rademacherMenshov_majorant (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (w : ℕ → ℝ) (hw : ∀ i,0 ≤ w i)
    {B : ℝ} (hB : 0 ≤ B) (hI : ∀ k b,‖intervalL2Sum b (2^k) F‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ K, K ≤ 2^h → ∀ x,‖intervalL2Sum a K F x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h) w) := by
  refine ⟨prefixL2Majorant h a F,prefixL2Majorant_nonneg h a F,
    fun K hK x => prefixL2Majorant_dominates h a K F hK x,?_⟩
  rw [prefixL2Majorant_norm]
  have hn := intervalRealBudget_nonneg a (2^h) w hw
  have he := binaryTree_uniform_budget h a F w B hI
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
