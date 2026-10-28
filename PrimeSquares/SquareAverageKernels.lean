import PrimeSquares.FiniteSquareOperators
import PrimeSquares.RestrictedL2
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Actual square-average kernels and their local bounds

The finite kernel is identified with the continuous weighted translation
operator. Positive weights give positivity, pointwise domination, finite
spatial support and the exact local l1 bound needed by the abstract theorem.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem natSquare_int_injective : Function.Injective (fun n : ℕ => (n : ℤ)^2) := by
  intro m n h
  exact_mod_cast (sq_eq_sq₀ (Int.natCast_nonneg m) (Int.natCast_nonneg n)).mp h

noncomputable def finiteSquareKernel (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (z : ℤ) : ℂ :=
  (c : ℂ) * ∑ n ∈ S, if z = (n : ℤ)^2 then (w n : ℂ) else 0

theorem finiteSquareKernel_at_square (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (m : ℕ) :
    finiteSquareKernel S c w ((m : ℤ)^2) = if m ∈ S then (c : ℂ) * (w m : ℂ) else 0 := by
  have he (n : ℕ) : (m : ℤ)^2 = (n : ℤ)^2 ↔ m = n := natSquare_int_injective.eq_iff
  simp only [finiteSquareKernel, he, sum_ite_eq]
  split_ifs <;> simp

theorem finiteSquareKernel_eq_zero (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) {z : ℤ}
    (hz : z ∉ S.image (fun n : ℕ => (n : ℤ)^2)) : finiteSquareKernel S c w z = 0 := by
  unfold finiteSquareKernel
  have hs : (∑ n ∈ S, if z = (n : ℤ)^2 then (w n : ℂ) else 0) = 0 := by
    apply sum_eq_zero
    intro n hn
    exact ite_eq_right (fun he => hz (mem_image.mpr ⟨n, hn, he.symm⟩))
  rw [hs, mul_zero]

theorem finiteSquareKernel_nonnegative (S : Finset ℕ) {c : ℝ} (hc : 0 ≤ c)
    (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) : NonnegativeKernel (finiteSquareKernel S c w) := by
  intro z
  by_cases hz : z ∈ S.image (fun n : ℕ => (n : ℤ)^2)
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    rw [finiteSquareKernel_at_square, ite_eq_left hn]
    constructor
    · simp
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        mul_nonneg hc (hw n hn)
  · rw [finiteSquareKernel_eq_zero S c w hz]
    simp

theorem finiteSquareKernel_norm_le (S : Finset ℕ) {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) (hb : ∀ n ∈ S, w n ≤ B) (z : ℤ) :
    ‖finiteSquareKernel S c w z‖ ≤ c * B := by
  by_cases hz : z ∈ S.image (fun n : ℕ => (n : ℤ)^2)
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    rw [finiteSquareKernel_at_square, ite_eq_left hn, ← Complex.ofReal_mul,
      Complex.norm_of_nonneg (mul_nonneg hc (hw n hn))]
    exact mul_le_mul_of_nonneg_left (hb n hn) hc
  · rw [finiteSquareKernel_eq_zero S c w hz, norm_zero]
    exact mul_nonneg hc hB

theorem finiteSquareKernel_re_domination (S : Finset ℕ) {c B : ℝ} (hc : 0 ≤ c)
    (w v : ℕ → ℝ) (hwv : ∀ n ∈ S, w n ≤ B * v n) (z : ℤ) :
    (finiteSquareKernel S c w z).re ≤ B * (finiteSquareKernel S c v z).re := by
  by_cases hz : z ∈ S.image (fun n : ℕ => (n : ℤ)^2)
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    simp only [finiteSquareKernel_at_square, ite_eq_left hn,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact (mul_le_mul_of_nonneg_left (hwv n hn) hc).trans_eq (by ring)
  · rw [finiteSquareKernel_eq_zero S c w hz, finiteSquareKernel_eq_zero S c v hz]
    simp

theorem finiteSquareKernel_indicator_domination (S : Finset ℕ) {c B : ℝ} (hc : 0 ≤ c)
    (w v : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) (hwv : ∀ n ∈ S, w n ≤ B * v n)
    (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (finiteSquareKernel S c w) F x‖ ≤
      B * (indicatorConvolution (finiteSquareKernel S c v) F x).re := by
  have hK := finiteSquareKernel_nonnegative S hc w hw
  rw [complex_norm_eq_re (indicatorConvolution_im_zero hK F x)
    (indicatorConvolution_re_nonneg hK F x)]
  simp only [indicatorConvolution, Complex.re_sum, mul_sum]
  exact sum_le_sum fun y _ => finiteSquareKernel_re_domination S hc w v hwv (x-y)

theorem finiteSquareKernel_finiteInput {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    finiteConvolution (finiteSquareKernel S c w) F f x =
      finiteSquareOperator hp S c w (finiteInputLp F f P) x := by
  rw [finiteSquareOperator_apply]
  unfold finiteConvolution finiteSquareKernel
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  have he (y : ℤ) : x-y = (n : ℤ)^2 ↔ y = x-(n : ℤ)^2 := by omega
  simp only [ite_mul, zero_mul, he, sum_ite_eq', finiteInputLp_apply]
  split_ifs <;> simp

theorem finiteSquareKernel_l2_bound (S : Finset ℕ) {c : ℝ} (hc : 0 ≤ c)
    (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) :
    KernelL2Bound (finiteSquareKernel S c w) (c * ∑ n ∈ S, w n) := by
  refine ⟨finiteSquareOperator (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) S c w, ?_,
    finiteSquareOperator_norm_le_mass (by norm_num) S hc w hw⟩
  intro F x
  rw [← finiteInputLp_one, ← finiteConvolution_indicator]
  exact finiteSquareKernel_finiteInput (by norm_num) S c w F (fun _ => 1) x

def squareAverageWindow (N : ℕ) (x : ℤ) : Finset ℤ := Icc (x-(N : ℤ)^2) x

theorem finiteSquareKernel_support_interval (S : Finset ℕ) (N : ℕ)
    (hS : S ⊆ Ioc 0 N) (c : ℝ) (w : ℕ → ℝ) {z : ℤ}
    (hz : z ∉ Icc 1 ((N : ℤ)^2)) : finiteSquareKernel S c w z = 0 := by
  apply finiteSquareKernel_eq_zero
  intro himage
  obtain ⟨n, hn, he⟩ := mem_image.mp himage
  have hn0 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (mem_Ioc.mp (hS hn)).1
  have hnN : (n : ℤ) ≤ N := by exact_mod_cast (mem_Ioc.mp (hS hn)).2
  have hsquare : (n : ℤ)^2 ≤ (N : ℤ)^2 := pow_le_pow_left₀ (Int.natCast_nonneg n) hnN 2
  apply hz
  rw [← he]
  exact mem_Icc.mpr ⟨by nlinarith, hsquare⟩

theorem finiteSquareKernel_localization (S : Finset ℕ) (N : ℕ)
    (hS : S ⊆ Ioc 0 N) (c : ℝ) (w : ℕ → ℝ) (F : Finset ℤ) (x : ℤ) :
    indicatorConvolution (finiteSquareKernel S c w) F x =
      indicatorConvolution (finiteSquareKernel S c w) (F ∩ squareAverageWindow N x) x := by
  unfold indicatorConvolution
  symm
  apply sum_subset (inter_subset_left)
  intro y hyF hy
  apply finiteSquareKernel_eq_zero
  intro hz
  obtain ⟨n, hn, he⟩ := mem_image.mp hz
  have hnN : n ≤ N := (mem_Ioc.mp (hS hn)).2
  have hsquare : (n : ℤ)^2 ≤ (N : ℤ)^2 := by
    exact pow_le_pow_left₀ (Int.natCast_nonneg n) (by exact_mod_cast hnN) 2
  have hnonneg : 0 ≤ (n : ℤ)^2 := sq_nonneg _
  have hwin : y ∈ squareAverageWindow N x := by
    simp only [squareAverageWindow, mem_Icc]
    constructor <;> omega
  exact hy (mem_inter.mpr ⟨hyF, hwin⟩)

theorem finiteSquareKernel_local_bound (S : Finset ℕ) (N : ℕ)
    (hS : S ⊆ Ioc 0 N) {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) (hb : ∀ n ∈ S, w n ≤ B)
    (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (finiteSquareKernel S c w) F x‖ ≤
      (c * B) * ‖finiteIndicatorLp (F ∩ squareAverageWindow N x) 1‖ := by
  rw [finiteSquareKernel_localization S N hS c w F x, finiteIndicatorLp_one_norm]
  exact (indicatorConvolution_norm_le _ _ (c*B)
    (finiteSquareKernel_norm_le S hc hB w hw hb) x).trans_eq (by ring)

end PrimeSquares
