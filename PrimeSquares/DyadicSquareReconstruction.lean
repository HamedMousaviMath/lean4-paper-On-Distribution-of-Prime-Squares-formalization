import PrimeSquares.PrimeSquareAverages

/-!
# Exact annular identities and reconstruction

These are equalities of the actual continuous operators, for arbitrary
real weights. Lambda(1)=0 removes the bottom term for prime-power averages;
ordinary square averages retain the source's N^-1 translation by one.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem square_half_normalization (M : ℕ) :
    (1/2 : ℂ) * Complex.ofReal ((M : ℝ)⁻¹) =
      Complex.ofReal (((2*M : ℕ) : ℝ)⁻¹) := by
  push_cast
  simp only [mul_inv_rev]
  ring

theorem annularWeightedSquareAverage_two_mul {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (M : ℕ) (w : ℕ → ℝ) :
    annularWeightedSquareAverage hp (2*M) w =
      weightedSquareAverage hp (2*M) w - (1/2 : ℂ) • weightedSquareAverage hp M w := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change annularWeightedSquareAverage hp (2*M) w f x =
    weightedSquareAverage hp (2*M) w f x - (1/2 : ℂ) * weightedSquareAverage hp M w f x
  rw [annularWeightedSquareAverage_apply, weightedSquareAverage_apply, weightedSquareAverage_apply]
  rw [show (2*M)/2 = M by omega]
  have hsum := sum_Ioc_consecutive (fun n : ℕ => (w n : ℂ) * f (x-(n : ℤ)^2))
    (Nat.zero_le M) (show M ≤ 2*M by omega)
  rw [← hsum]
  rw [← mul_assoc, square_half_normalization]
  ring

theorem weightedSquareAverage_one {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (w : ℕ → ℝ) :
    weightedSquareAverage hp 1 w = (w 1 : ℂ) • integerTranslate hp 1 := by
  norm_num [weightedSquareAverage, finiteSquareOperator]

theorem weightedSquareAverage_dyadic_weighted {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (w : ℕ → ℝ) (k : ℕ) :
    (2 : ℂ)^k • weightedSquareAverage hp (2^k) w =
      (w 1 : ℂ) • integerTranslate hp 1 +
        ∑ j ∈ range k, (2 : ℂ)^(j+1) • annularWeightedSquareAverage hp (2^(j+1)) w := by
  induction k with
  | zero => simp [weightedSquareAverage_one]
  | succ k ih =>
    have hstep : weightedSquareAverage hp (2^(k+1)) w =
        annularWeightedSquareAverage hp (2^(k+1)) w +
          (1/2 : ℂ) • weightedSquareAverage hp (2^k) w := by
      have h := annularWeightedSquareAverage_two_mul hp (2^k) w
      have he : 2*(2^k) = 2^(k+1) := by rw [pow_succ]; omega
      rw [he] at h
      exact sub_eq_iff_eq_add.mp h.symm
    have hc : (2 : ℂ)^(k+1) * (1/2 : ℂ) = (2 : ℂ)^k := by rw [pow_succ]; ring
    rw [hstep, smul_add, smul_smul, hc, ih, sum_range_succ]
    abel

theorem weightedSquareAverage_dyadic_reconstruction {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (w : ℕ → ℝ) (k : ℕ) :
    weightedSquareAverage hp (2^k) w =
      ((w 1 : ℂ)/(2 : ℂ)^k) • integerTranslate hp 1 +
        ∑ j ∈ range k, ((2 : ℂ)^(j+1)/(2 : ℂ)^k) •
          annularWeightedSquareAverage hp (2^(j+1)) w := by
  have hn : (2 : ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = ((2 : ℂ)^k)⁻¹ • ((2 : ℂ)^k • weightedSquareAverage hp (2^k) w) := by
      rw [inv_smul_smul₀ hn]
    _ = _ := by
      rw [weightedSquareAverage_dyadic_weighted, smul_add, smul_sum]
      simp only [smul_smul, div_eq_mul_inv, mul_comm]

theorem weightedSquareAverage_dyadic_descending {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (w : ℕ → ℝ) (k : ℕ) :
    weightedSquareAverage hp (2^k) w =
      ((w 1 : ℂ)/(2 : ℂ)^k) • integerTranslate hp 1 +
        ∑ j ∈ range k, ((2 : ℂ)^j)⁻¹ • annularWeightedSquareAverage hp (2^(k-j)) w := by
  rw [weightedSquareAverage_dyadic_reconstruction]
  congr 1
  rw [← sum_range_reflect (fun j => ((2 : ℂ)^(j+1)/(2 : ℂ)^k) •
    annularWeightedSquareAverage hp (2^(j+1)) w) k]
  apply sum_congr rfl
  intro j hj
  have hjk : j < k := mem_range.mp hj
  rw [show k-1-j+1 = k-j by omega]
  have hpow : (2 : ℂ)^k = (2 : ℂ)^(k-j) * (2 : ℂ)^j := by
    rw [← pow_add, Nat.sub_add_cancel hjk.le]
  have hc : (2 : ℂ)^(k-j)/(2 : ℂ)^k = ((2 : ℂ)^j)⁻¹ := by
    rw [hpow]
    have ha : (2 : ℂ)^(k-j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hb : (2 : ℂ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [hc]

theorem mangoldtSquareAverage_dyadic_reconstruction {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (k : ℕ) :
    weightedSquareAverage hp (2^k) ArithmeticFunction.vonMangoldt =
      ∑ j ∈ range k, ((2 : ℂ)^j)⁻¹ •
        annularWeightedSquareAverage hp (2^(k-j)) ArithmeticFunction.vonMangoldt := by
  have hz : ((0 : ℂ)/(2 : ℂ)^k) • integerTranslate (P := P) hp 1 = 0 := by
    rw [zero_div]
    exact zero_smul ℂ (integerTranslate (P := P) hp 1)
  simpa only [ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero, hz, zero_add] using
    weightedSquareAverage_dyadic_descending (P := P) hp ArithmeticFunction.vonMangoldt k

theorem ordinarySquareAverage_dyadic_reconstruction {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (k : ℕ) :
    weightedSquareAverage hp (2^k) (fun _ => 1) =
      ((2 : ℂ)^k)⁻¹ • integerTranslate hp 1 +
        ∑ j ∈ range k, ((2 : ℂ)^j)⁻¹ •
          annularWeightedSquareAverage hp (2^(k-j)) (fun _ => 1) := by
  simpa only [Complex.ofReal_one, one_div] using
    weightedSquareAverage_dyadic_descending hp (fun _ => 1) k

end PrimeSquares
