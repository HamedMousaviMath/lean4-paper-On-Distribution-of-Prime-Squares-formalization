import PrimeSquares.GoldbachSieveRootCounts

set_option autoImplicit false
namespace PrimeSquares

noncomputable def goldbachLocalDensity (R : ℝ) (p : ℕ) (a b : ℤ) : ℝ :=
  if (p:ℝ)≤R then (goldbachRho p a:ℝ)/((p:ℝ)-1-(goldbachRho p b:ℝ))
  else 1/((p:ℝ)-1)

noncomputable def goldbachLowerDensity (R : ℝ) (n : ℤ) (p : ℕ) : ℝ :=
  goldbachLocalDensity R p (n-1) n

noncomputable def goldbachUpperDensity (R : ℝ) (n : ℤ) (p : ℕ) : ℝ :=
  goldbachLocalDensity R p n (n-1)

theorem goldbach_local_denominator_pos (p : ℕ) [Fact p.Prime] (hp : 3 < p) (b : ℤ) :
    0 < (p:ℝ)-1-(goldbachRho p b:ℝ) := by
  have hr : (goldbachRho p b:ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) b
  have hp' : (3:ℝ) < p := by exact_mod_cast hp
  linarith

theorem goldbach_local_density_nonneg (R : ℝ) (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (a b : ℤ) : 0≤goldbachLocalDensity R p a b := by
  unfold goldbachLocalDensity
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (goldbach_local_denominator_pos p hp b).le
  · have hp' : (3:ℝ) < p := by exact_mod_cast hp
    exact div_nonneg zero_le_one (by linarith)

theorem goldbach_local_density_le (R : ℝ) (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (a b : ℤ) : goldbachLocalDensity R p a b≤2/((p:ℝ)-3) := by
  have hp' : (3:ℝ) < p := by exact_mod_cast hp
  have h3 : 0 < (p:ℝ)-3 := by linarith
  have hr : (goldbachRho p b:ℝ)≤2 := by exact_mod_cast goldbach_rho_le_two p (by omega) b
  unfold goldbachLocalDensity
  split_ifs
  · apply (div_le_div_of_nonneg_right (show (goldbachRho p a:ℝ)≤2 by
        exact_mod_cast goldbach_rho_le_two p (by omega) a)
        (goldbach_local_denominator_pos p hp b).le).trans
    exact div_le_div_of_nonneg_left (by norm_num) h3 (by linarith)
  · exact (div_le_div_iff₀ (by linarith : 0 < (p:ℝ)-1) h3).mpr (by linarith)

theorem goldbach_density_bound_lt_one (p : ℕ) (hp : 7≤p) :
    2/((p:ℝ)-3) < 1 := by
  have hp' : (7:ℝ)≤p := by exact_mod_cast hp
  apply (div_lt_one (by linarith : 0 < (p:ℝ)-3)).mpr
  linarith

theorem goldbach_local_density_lt_one (R : ℝ) (p : ℕ) [Fact p.Prime]
    (hp : 7≤p) (a b : ℤ) : goldbachLocalDensity R p a b < 1 :=
  (goldbach_local_density_le R p (by omega) a b).trans_lt (goldbach_density_bound_lt_one p hp)

theorem goldbach_upper_density_five (R : ℝ) (n : ℤ) :
    goldbachUpperDensity R n 5≤1/2 := by
  unfold goldbachUpperDensity goldbachLocalDensity
  split_ifs
  · rcases goldbach_rho_five_consecutive n with h | ⟨h,h'⟩
    · simp only [h,Nat.cast_zero,zero_div];norm_num
    · simp only [h,h',Nat.cast_ofNat,Nat.cast_zero];norm_num
  · norm_num

theorem goldbach_upper_density_range (R : ℝ) (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (n : ℤ) :
    0≤goldbachUpperDensity R n p ∧ goldbachUpperDensity R n p < 1 := by
  refine ⟨goldbach_local_density_nonneg R p hp n (n-1),?_⟩
  by_cases hp5 : p=5
  · subst p
    exact (goldbach_upper_density_five R n).trans_lt (by norm_num)
  · have hprime : p.Prime := Fact.out
    have h7 : 7≤p := by
      have h4 : p≠4 := by
        intro h
        exact (by decide : ¬Nat.Prime 4) (h ▸ hprime)
      have h6 : p≠6 := by
        intro h
        exact (by decide : ¬Nat.Prime 6) (h ▸ hprime)
      omega
    exact goldbach_local_density_lt_one R p h7 n (n-1)

end PrimeSquares
