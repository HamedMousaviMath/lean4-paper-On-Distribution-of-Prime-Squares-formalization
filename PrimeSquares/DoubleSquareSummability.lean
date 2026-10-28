import PrimeSquares.L2SquareEnergy

open scoped lp
namespace PrimeSquares

theorem joint_square_summable (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Summable (fun p : ℕ × ℤ => ‖F p.1 p.2‖^2) := by
  apply (summable_prod_of_nonneg (fun p : ℕ × ℤ => sq_nonneg ‖F p.1 p.2‖)).mpr
  exact ⟨fun j => (l2_square_hasSum (F j)).summable,by simpa only [l2_square_tsum] using hF⟩

theorem joint_square_summable_swap (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) :
    Summable (fun p : ℤ × ℕ => ‖F p.2 p.1‖^2) := by
  have h : Summable ((fun p : ℕ × ℤ => ‖F p.1 p.2‖^2) ∘ (Equiv.prodComm ℤ ℕ)) :=
    (joint_square_summable F hF).comp_injective (i := Equiv.prodComm ℤ ℕ) (Equiv.prodComm ℤ ℕ).injective
  exact h

theorem coordinate_square_summable (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (x : ℤ) :
    Summable (fun j : ℕ => ‖F j x‖^2) :=
  ((summable_prod_of_nonneg (fun p : ℤ × ℕ => sq_nonneg ‖F p.2 p.1‖)).mp
    (joint_square_summable_swap F hF)).1 x

end PrimeSquares
