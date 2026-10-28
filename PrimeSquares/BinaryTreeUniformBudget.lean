import PrimeSquares.IntervalRealBudget
open scoped lp
namespace PrimeSquares
theorem binaryTree_uniform_budget (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (w : ℕ → ℝ) (B : ℝ)
    (hI : ∀ k b,‖intervalL2Sum b (2^k) F‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    binaryTreeL2Energy h a F ≤ (h+1 : ℝ)*B^2*intervalRealBudget a (2^h) w := by
  induction h generalizing a with
  | zero => simpa only [intervalL2Sum,intervalRealBudget,pow_zero,Finset.sum_range_one,Nat.add_zero,
      Nat.cast_zero,zero_add,one_mul,binaryTreeL2Energy] using hI 0 a
  | succ h ih =>
    have hb := hI (h+1) a
    have hl := ih a
    have hr := ih (a+2^h)
    have he : intervalRealBudget a (2^(h+1)) w=
        intervalRealBudget a (2^h) w+intervalRealBudget (a+2^h) (2^h) w := by
      rw [pow_succ,show 2^h*2=2^h+2^h by omega,intervalRealBudget_add]
    change ‖intervalL2Sum a (2^(h+1)) F‖^2+_+_ ≤ _
    rw [he] at hb ⊢
    push_cast
    nlinarith
end PrimeSquares
