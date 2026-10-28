import PrimeSquares.GaussProduct
import PrimeSquares.PrimeFactorEstimates

/-! Elementary logarithmic estimates for the proved finite Gauss majorant. -/

open Finset

namespace PrimeSquares

theorem gaussOddPrimeFactor_le_four (p : ℕ) (hp : 2 ≤ p) :
    gaussOddPrimeFactor p ≤ 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs0 := Real.sqrt_nonneg (p : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg p)
  have hs : 0 < Real.sqrt (p : ℝ) := by nlinarith
  have hi : (Real.sqrt (p : ℝ))⁻¹ ≤ 3 / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hs]
    nlinarith
  have hd : 0 < 1 - (Real.sqrt (p : ℝ))⁻¹ := by linarith
  change (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹ ≤ 4
  rw [inv_eq_one_div, div_le_iff₀ hd]
  linarith

theorem log_gaussOddPrimeFactor_le (p : ℕ) (hp : 2 ≤ p) :
    Real.log (gaussOddPrimeFactor p) ≤ (Real.sqrt (p : ℝ))⁻¹ + 4 * (p : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hi : (Real.sqrt (p : ℝ))⁻¹ < 1 :=
    (inv_lt_one₀ hs).mpr (by nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ)])
  have hd : 1 - (Real.sqrt (p : ℝ))⁻¹ ≠ 0 := by linarith
  have hf : gaussOddPrimeFactor p * (1 - (Real.sqrt (p : ℝ))⁻¹) = 1 :=
    inv_mul_cancel₀ hd
  have hr2 : ((Real.sqrt (p : ℝ))⁻¹) ^ 2 = (p : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  have he : gaussOddPrimeFactor p - 1 =
      (Real.sqrt (p : ℝ))⁻¹ + (p : ℝ)⁻¹ * gaussOddPrimeFactor p := by
    rw [← hr2]
    have hfr := congrArg (fun x : ℝ => (Real.sqrt (p : ℝ))⁻¹ * x) hf
    nlinarith [hfr]
  calc
    _ ≤ gaussOddPrimeFactor p - 1 := Real.log_le_sub_one_of_pos (gaussOddPrimeFactor_pos p hp)
    _ = _ := he
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (gaussOddPrimeFactor_le_four p hp)
        (inv_nonneg.mpr (Nat.cast_nonneg p))
      nlinarith [h]

theorem log_gaussOddProduct_le (q : ℕ) :
    Real.log (gaussOddProduct q) ≤
      (∑ p ∈ q.primeFactors, (Real.sqrt (p : ℝ))⁻¹) +
        4 * ∑ p ∈ q.primeFactors, (p : ℝ)⁻¹ := by
  classical
  rw [gaussOddProduct, Real.log_prod]
  · calc
      _ ≤ ∑ p ∈ q.primeFactors.filter (fun p => 2 < p),
          ((Real.sqrt (p : ℝ))⁻¹ + 4 * (p : ℝ)⁻¹) := by
        apply sum_le_sum
        intro p hp
        exact log_gaussOddPrimeFactor_le p (le_of_lt (mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ q.primeFactors, ((Real.sqrt (p : ℝ))⁻¹ + 4 * (p : ℝ)⁻¹) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p hp _; positivity
      _ = _ := by rw [sum_add_distrib, ← mul_sum]
  · intro p hp
    exact ne_of_gt (gaussOddPrimeFactor_pos p (le_of_lt (mem_filter.mp hp).2))

theorem log_four_mul_gaussOddProduct_bound (q : ℕ) (hq : 0 < q)
    (hL : 2 ≤ Real.log q) :
    Real.log (4 * gaussOddProduct q) ≤ Real.log 4 + primeInvSqrtSum (Real.log q) +
      (Real.log q - primeTheta (Real.log q)) /
        (Real.sqrt (Real.log q) * Real.log (Real.log q)) +
      4 * (1 + Real.log (Real.log q) + (Real.log 2)⁻¹) := by
  have hp : 0 < gaussOddProduct q :=
    prod_pos fun p hp => gaussOddPrimeFactor_pos p (le_of_lt (mem_filter.mp hp).2)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hp.ne']
  have h1 := log_gaussOddProduct_le q
  have h2 := primeFactors_inv_sqrt_threshold q hq (Real.log q) hL
  have h3 := primeFactors_reciprocal_bound q hq hL
  linarith

end PrimeSquares
