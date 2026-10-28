import PrimeSquares.FiniteMaximalEnvelopeBound

open Finset
open scoped lp
namespace PrimeSquares

/-- Join finitely many initial operator outputs to a uniformly dominated tail.
The norm cost is the number of initial scales times their operator bound. -/
theorem initialScale_maximal_completion
    (T : ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)) (n : ℕ) {A B : ℝ}
    (hT : ∀ j ∈ range n,‖T j‖ ≤ A) (f : ℓ²(ℤ,ℂ))
    (u : lp (fun _ : ℤ => ℝ) 2) (hu : ∀ x,0 ≤ u x)
    (htail : ∀ j x,‖T (n+j) f x‖ ≤ u x) (hnorm : ‖u‖ ≤ B*‖f‖) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖T j f x‖ ≤ g x) ∧ ‖g‖ ≤ ((n : ℝ)*A+B)*‖f‖ := by
  let v := finiteOperatorEnvelope (range n) T f
  refine ⟨v+u,fun x => add_nonneg (finiteOperatorEnvelope_nonneg _ _ _ x) (hu x),?_,?_⟩
  · intro j x
    by_cases hj : j < n
    · exact (finiteOperatorEnvelope_dominates (range n) T f (mem_range.mpr hj) x).trans
        (le_add_of_nonneg_right (hu x))
    · have hjn : n ≤ j := le_of_not_gt hj
      have ht := htail (j-n) x
      rw [Nat.add_sub_of_le hjn] at ht
      exact ht.trans (le_add_of_nonneg_left (finiteOperatorEnvelope_nonneg _ _ _ x))
  · have hv : ‖v‖ ≤ ((n : ℝ)*A)*‖f‖ := by
      simpa only [sum_const,card_range,nsmul_eq_mul] using
        finiteOperatorEnvelope_norm (range n) T (fun _ => A) hT f
    exact (norm_add_le v u).trans ((add_le_add hv hnorm).trans_eq (by ring))

end PrimeSquares
