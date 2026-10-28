import PrimeSquares.IndependentStoppingInputs
import PrimeSquares.AdmissibleAnnularLinearization
import PrimeSquares.IndependentSquareDecomposition

/-! # Actual small-scale prime-square domination by full ordinary-square averages -/

open Finset
namespace PrimeSquares

theorem ordinaryDyadicValue_positive (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    (ordinaryDyadicValue j F x).im = 0 ∧ 0 ≤ (ordinaryDyadicValue j F x).re := by
  have hK := finiteSquareKernel_nonnegative (Ioc 0 ((2 : ℕ)^j*2))
    (by positivity : 0 ≤ ((((2 : ℕ)^j*2 : ℕ) : ℝ)⁻¹)) (fun _ => (1 : ℝ)) (fun _ _ => by norm_num)
  exact ⟨indicatorConvolution_im_zero hK F x, indicatorConvolution_re_nonneg hK F x⟩

theorem annularDyadicValue_square_domination (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    ‖annularDyadicValue j F x‖ ≤ Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ) *
      ‖ordinaryDyadicValue j F x‖ := by
  have hN : 2 ≤ (2 : ℕ)^j*2 := by
    have hp : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by decide)
    omega
  have hlog : 0 ≤ Real.log (((2 : ℕ)^j*2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (2 : ℕ)^j*2))
  have hK := finiteSquareKernel_nonnegative (Ioc 0 ((2 : ℕ)^j))
    (by positivity : 0 ≤ ((((2 : ℕ)^j : ℕ) : ℝ)⁻¹)) (fun _ => (1 : ℝ)) (fun _ _ => by norm_num)
  have hm := indicatorConvolution_re_nonneg hK F x
  have hd := congrArg Complex.re (annular_indicator_two_mul ((2 : ℕ)^j) (fun _ => 1) F x)
  norm_num at hd
  rw [Nat.mul_comm 2 ((2 : ℕ)^j)] at hd
  change 0 ≤ (indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^j) (fun _ => 1)) F x).re at hm
  have ha : (indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^j*2)
      (fun _ => 1)) F x).re ≤ (ordinaryDyadicValue j F x).re := by
    change _ ≤ (indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^j*2) (fun _ => 1)) F x).re
    nlinarith
  have hh := (annularMangoldt_indicator_domination ((2 : ℕ)^j*2) F x).trans
    (mul_le_mul_of_nonneg_left ha hlog)
  have hp := ordinaryDyadicValue_positive j F x
  rw [← complex_norm_eq_re hp.1 hp.2] at hh
  exact hh

theorem primeSmallStopping_square_domination (F G : Finset ℤ) (τ : ℤ → ℕ) (N₀ : ℝ)
    (hτ : ∀ x ∈ G, (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ) ≤ N₀) :
    ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖ ≤ Real.log N₀ *
      ‖∑ x ∈ G, ordinaryDyadicValue (τ x) F x‖ := by
  rw [finite_positive_pairing_norm G _ (fun x _ => annularDyadicValue_positive _ _ x),
    finite_positive_pairing_norm G _ (fun x _ => ordinaryDyadicValue_positive _ _ x), mul_sum]
  apply sum_le_sum
  intro x hx
  exact (annularDyadicValue_square_domination (τ x) F x).trans
    (mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) (hτ x hx)) (norm_nonneg _))

end PrimeSquares
