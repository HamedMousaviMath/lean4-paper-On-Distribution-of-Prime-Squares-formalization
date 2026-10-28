import PrimeSquares.SummableOperatorSquares

open scoped lp
namespace PrimeSquares

theorem square_tail_summable (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (J : ℕ) :
    Summable (fun j : ℕ => ‖F (J+j)‖^2) := hF.comp_injective (add_right_injective J)

theorem squareMaximum_tail_norm (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2)) (J : ℕ) :
    ‖squareMaximumL2 (fun j => F (J+j)) (square_tail_summable F hF J)‖ ≤ Real.sqrt (∑' j : ℕ,‖F (J+j)‖^2) :=
  squareMaximumL2_norm _ _

theorem squareMaximum_tail_value_mono (F : ℕ → ℓ²(ℤ, ℂ)) (hF : Summable (fun j : ℕ => ‖F j‖^2))
    {J K : ℕ} (hJK : J ≤ K) (x : ℤ) :
    squareMaximumValue (fun j => F (K+j)) x ≤ squareMaximumValue (fun j => F (J+j)) x := by
  apply ciSup_le
  intro j
  have hd := le_ciSup (squareMaximumValue_bddAbove (fun m => F (J+m)) (square_tail_summable F hF J) x) (K-J+j)
  have he : K+j=J+(K-J+j) := by omega
  have hl : ‖F (K+j) x‖=‖F (J+(K-J+j)) x‖ := congrArg (fun n : ℕ => ‖F n x‖) he
  exact hl.trans_le hd

end PrimeSquares
