import PrimeSquares.Proposition419
import PrimeSquares.SourceHighOrliczUniform

/-! # The bounded dyadic Q range in the sharp high factor -/

open Finset
namespace PrimeSquares

theorem regularizedHighFactor_dyadic (c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      Real.exp (c₁*regularizedHighExponentWeight ((2 : ℝ)^j)) ≤
        C * orliczHighFactor c₁ (1/2) ((2 : ℝ)^j) := by
  let D := fun j : ℕ => Real.exp (c₁*(regularizedHighExponentWeight ((2 : ℝ)^j) -
    (Real.log ((2 : ℝ)^j))^(1/2 : ℝ)/Real.log (Real.log ((2 : ℝ)^j))))
  let C := 1 + ∑ j ∈ range 4, D j
  have hD : ∀ j, 0 ≤ D j := fun _ => (Real.exp_pos _).le
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (sum_nonneg (fun j _ => hD j))
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro j
  by_cases hj : j < 4
  · have hd : D j ≤ C := by
      have hs := Finset.single_le_sum (s := range 4) (f := D) (fun i _ => hD i) (mem_range.mpr hj)
      dsimp [C]
      linarith
    have he : Real.exp (c₁*regularizedHighExponentWeight ((2 : ℝ)^j)) =
        D j * orliczHighFactor c₁ (1/2) ((2 : ℝ)^j) := by
      dsimp [D, orliczHighFactor]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
  · have hQ : (16 : ℝ) ≤ (2 : ℝ)^j := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 4 ≤ j)
      norm_num only [show (2 : ℝ)^(4 : ℕ)=16 by norm_num] at hp
      exact hp
    have hlog16 : (2 : ℝ) ≤ Real.log 16 := by
      rw [show (16 : ℝ)=4^2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [log_four_one_le]
    have hlog := hlog16.trans (Real.log_le_log (by norm_num : (0 : ℝ)<16) hQ)
    have he : Real.exp (c₁*regularizedHighExponentWeight ((2 : ℝ)^j)) =
        orliczHighFactor c₁ (1/2) ((2 : ℝ)^j) := by
      rw [regularizedHighExponentWeight_eq hlog, Real.sqrt_eq_rpow]
      unfold orliczHighFactor
      congr 1
      ring
    rw [he]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hC1

end PrimeSquares
