import PrimeSquares.RealDenominatorBandDifference
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem realPrefix_difference_majorant (L : ℕ) (m : ℕ → C(PrimeCircle,ℂ)) (f : ℓ²(ℤ,ℂ))
    (g : lp (fun _ : ℤ => ℝ) 2) (hg : ∀ x,0 ≤ g x)
    (ht : ∀ R,0 ≤ R → ∀ x,‖integerMultiplier (realTruncatedCircleSymbol L R m) f x‖ ≤ g x) :
    ∃ u : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ u x) ∧
      (∀ Q R,0 ≤ Q → 0 ≤ R → ∀ x,
        ‖integerMultiplier (realTruncatedCircleSymbol L R m-realTruncatedCircleSymbol L Q m) f x‖ ≤ u x) ∧
      ‖u‖ ≤ 2*‖g‖ := by
  refine ⟨(2 : ℝ) • g,fun x => by change 0 ≤ 2*g x;exact mul_nonneg (by norm_num) (hg x),?_,?_⟩
  · intro Q R hQ hR x
    rw [integerMultiplier_sub,_root_.sub_apply,lp.coeFn_sub,Pi.sub_apply]
    change ‖_ - _‖ ≤ 2*g x
    exact (norm_sub_le _ _).trans (by linarith [ht R hR x,ht Q hQ x])
  · simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2),le_refl]
end PrimeSquares
