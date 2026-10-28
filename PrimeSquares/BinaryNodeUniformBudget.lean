import PrimeSquares.TimePrefixL2Majorant
open scoped lp
namespace PrimeSquares
theorem binaryNode_uniform_budget (h a : ℕ) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2)
    (w : ℕ → ℝ) (B : ℝ) (hI : ∀ k b,‖G k b‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    binaryNodeNormEnergy h a G ≤ (h+1 : ℝ)*B^2*intervalRealBudget a (2^h) w := by
  induction h generalizing a with
  | zero => simpa only [binaryNodeNormEnergy,Nat.cast_zero,zero_add,one_mul] using hI 0 a
  | succ h ih =>
    have hb := hI (h+1) a
    have hl := ih a
    have hr := ih (a+2^h)
    have he : intervalRealBudget a (2^(h+1)) w=
        intervalRealBudget a (2^h) w+intervalRealBudget (a+2^h) (2^h) w := by
      rw [pow_succ,show 2^h*2=2^h+2^h by omega,intervalRealBudget_add]
    change ‖G (h+1) a‖^2+_+_ ≤ _
    rw [he] at hb ⊢
    push_cast
    nlinarith
end PrimeSquares
