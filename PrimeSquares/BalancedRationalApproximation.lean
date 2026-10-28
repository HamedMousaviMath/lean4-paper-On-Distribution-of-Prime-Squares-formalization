import PrimeSquares.GhoshBalancedBound
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace PrimeSquares

theorem exists_balanced_rational_approximation (ξ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∃ r : ℚ, (r.den : ℝ) ≤ x^(3/2 : ℝ) ∧
      |ξ-(r : ℝ)| ≤ 1/((r.den : ℝ)*x^(3/2 : ℝ)) ∧
      |ξ-(r : ℝ)| < 1/(r.den : ℝ)^2 := by
  have hxp : 1 ≤ x^(3/2 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hn : 0 < ⌊x^(3/2 : ℝ)⌋₊ := by
    have hh : 1 ≤ ⌊x^(3/2 : ℝ)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hxp)
    omega
  obtain ⟨r,hr,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le ξ hn
  have hdp : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hdf : (r.den : ℝ) ≤ ⌊x^(3/2 : ℝ)⌋₊ := by exact_mod_cast hd
  have hfl := Nat.floor_le (by linarith : 0 ≤ x^(3/2 : ℝ))
  have hlt := Nat.lt_floor_add_one (x^(3/2 : ℝ))
  refine ⟨r,hdf.trans hfl,hr.trans ?_,hr.trans_lt ?_⟩
  · exact one_div_le_one_div_of_le (by positivity)
      (by nlinarith only [hlt.le,hdp])
  · apply one_div_lt_one_div_of_lt (sq_pos_of_pos hdp)
    nlinarith only [hdf,hdp]

theorem exists_balanced_annular_approximation (N : ℕ) (hN : 2 ≤ N) (ξ : ℝ) :
    ∃ r : ℚ, (r.den : ℝ) ≤ ((N : ℝ)/2)^(3/2 : ℝ) ∧
      |ξ-(r : ℝ)| ≤ 1/((r.den : ℝ)*((N : ℝ)/2)^(3/2 : ℝ)) ∧
      |ξ-(r : ℝ)| < 1/(r.den : ℝ)^2 := by
  apply exists_balanced_rational_approximation ξ
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

theorem balanced_approximation_representative_range {ξ x : ℝ} {r : ℚ}
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (hx : 1 ≤ x)
    (hr : |ξ-(r : ℝ)| ≤ 1/((r.den : ℝ)*x^(3/2 : ℝ))) :
    (r : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := by
  have hdp : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hp : 1 ≤ x^(3/2 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hb : 1/((r.den : ℝ)*x^(3/2 : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by nlinarith)
  obtain ⟨hl,hu⟩ := abs_le.mp (hr.trans hb)
  exact ⟨by linarith [hξ.1],by linarith [hξ.2]⟩

end PrimeSquares
