import PrimeSquares.DoubleSquareSummability

open scoped lp
namespace PrimeSquares

theorem coordinate_square_totals_summable (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Summable (fun x : ℤ => ∑' j : ℕ,‖F j x‖^2) :=
  ((summable_prod_of_nonneg (fun p : ℤ × ℕ => sq_nonneg ‖F p.2 p.1‖)).mp
    (joint_square_summable_swap F hF)).2

theorem coordinate_square_total (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    (∑' x : ℤ,∑' j : ℕ,‖F j x‖^2)=∑' j : ℕ,‖F j‖^2 := by
  calc
    _ = ∑' j : ℕ,∑' x : ℤ,‖F j x‖^2 :=
      Summable.tsum_comm (f := fun (j : ℕ) (x : ℤ) => ‖F j x‖^2) (joint_square_summable F hF)
    _ = _ := tsum_congr (fun j => l2_square_tsum (F j))

end PrimeSquares
