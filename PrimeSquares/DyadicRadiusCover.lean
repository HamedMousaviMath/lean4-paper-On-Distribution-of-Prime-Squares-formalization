import PrimeSquares.DecayProfile

namespace PrimeSquares

theorem dyadic_radius_cover {H : ℝ} (hH : 0 < H) (d : ℝ) :
    ∃ j : ℕ, |d| ≤ (2 : ℝ)^j*H := by
  obtain ⟨n,hn⟩ := exists_nat_gt (|d|/H)
  have hp : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n))
  exact ⟨n,(div_le_iff₀ hH).mp (hn.le.trans hp.le)⟩

noncomputable def dyadicRadiusLevel (H : ℝ) (hH : 0 < H) (d : ℝ) : ℕ :=
  Nat.find (dyadic_radius_cover hH d)

theorem dyadicRadiusLevel_upper (H : ℝ) (hH : 0 < H) (d : ℝ) :
    |d| ≤ (2 : ℝ)^(dyadicRadiusLevel H hH d)*H := by
  unfold dyadicRadiusLevel
  exact Nat.find_spec (dyadic_radius_cover hH d)

theorem dyadicRadiusLevel_minimal (H : ℝ) (hH : 0 < H) (d : ℝ) (j : ℕ)
    (hj : j < dyadicRadiusLevel H hH d) : (2 : ℝ)^j*H < |d| := by
  exact lt_of_not_ge (Nat.find_min (dyadic_radius_cover hH d) hj)

end PrimeSquares
