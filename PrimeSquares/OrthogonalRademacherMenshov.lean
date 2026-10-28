import PrimeSquares.OrthogonalL2IntervalEnergy
open scoped lp
namespace PrimeSquares
theorem orthogonal_rademacherMenshov (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ))
    (hF : ∀ i j,i ≠ j → inner ℂ (F i) (F j)=0) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ K,K ≤ 2^h → ∀ x,‖intervalL2Sum a K F x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*Real.sqrt (intervalRealBudget a (2^h) (fun i => ‖F i‖^2)) := by
  simpa only [mul_one] using rademacherMenshov_majorant h a F (fun i => ‖F i‖^2)
    (fun i => sq_nonneg _) (B := 1) (by norm_num)
    (fun k b => by rw [orthogonal_l2_interval_energy F hF];norm_num)
end PrimeSquares
