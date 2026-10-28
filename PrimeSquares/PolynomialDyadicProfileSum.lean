import PrimeSquares.RationalRelativeCutoffSum
import Mathlib.Analysis.SpecificLimits.Normed

open Finset
namespace PrimeSquares

theorem shifted_polynomial_geometric_summable (m : ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n : ℕ => ((n : ℝ)+1)^m*r^n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one m
    (by simpa only [Real.norm_eq_abs,abs_of_pos hr0] using hr1 : ‖r‖<1)
  have ht := ((summable_nat_add_iff 1).mpr hs).mul_left r⁻¹
  convert ht using 1
  ext n
  push_cast
  rw [pow_succ]
  field_simp

noncomputable def polynomialDyadicProfileConstant (δ : ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ)^m*(interpolationWeightConstant 1 1 δ δ+(2 : ℝ)^δ*
    ∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n)

theorem polynomialDyadicProfileConstant_nonneg {δ : ℝ} (hδ : 0<δ) (m : ℕ) :
    0 ≤ polynomialDyadicProfileConstant δ m := by
  have hI := interpolationWeightConstant_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) hδ hδ
  have ht : 0 ≤ ∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n := tsum_nonneg (fun n => by positivity)
  unfold polynomialDyadicProfileConstant
  positivity

theorem polynomial_dyadic_profile_summable {δ W : ℝ} (hδ : 0<δ) (hW : 0<W) (m : ℕ) :
    Summable (fun s : ℕ => ((s : ℝ)+1)^m*relativeCutoffProfile δ ((2 : ℝ)^s/W)) := by
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio hδ
  apply Summable.of_nonneg_of_le (fun n : ℕ => mul_nonneg (by positivity)
    (relativeCutoffProfile_nonneg (by positivity))) (f := fun n : ℕ =>
      W^δ*(((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n))
  · intro n
    calc
      _ ≤ ((n : ℝ)+1)^m*((2 : ℝ)^n/W)^(-δ) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by rw [dyadic_negative_ratio_factor hW];ring
  · exact (shifted_polynomial_geometric_summable m hr0 hr1).mul_left _

theorem polynomial_dyadic_profile_tsum {δ W : ℝ} (hδ : 0<δ) (hW : 1 ≤ W) (m : ℕ) :
    (∑' s : ℕ,((s : ℝ)+1)^m*relativeCutoffProfile δ ((2 : ℝ)^s/W)) ≤
      polynomialDyadicProfileConstant δ m*(1+Real.log W)^m := by
  have hWp : 0<W := by linarith
  obtain ⟨k,hk,hkup⟩ := exists_nat_pow_near hW (by norm_num : (1 : ℝ)<2)
  have hhigh : W ≤ 2*(2 : ℝ)^k := by simpa only [pow_succ,mul_comm] using hkup.le
  let w := fun n : ℕ => relativeCutoffProfile δ ((2 : ℝ)^n/W)
  have hw0 (n : ℕ) : 0 ≤ w n := relativeCutoffProfile_nonneg (by positivity)
  have hsum := polynomial_dyadic_profile_summable hδ hWp m
  have hs0 : Summable w := by
    convert interpolationWeight_summable (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) hδ hWp (a := δ) using 1
    ext n
    simp only [w,relativeCutoffProfile,interpolationWeight,one_mul]
  have hsum0 : (∑' n,w n) ≤ interpolationWeightConstant 1 1 δ δ := by
    simpa only [w,relativeCutoffProfile,interpolationWeight,one_mul] using
      interpolationWeight_tsum_le (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hδ hδ hWp
  have hhead : (∑ n ∈ range k,((n : ℝ)+1)^m*w n) ≤
      ((k : ℝ)+1)^m*interpolationWeightConstant 1 1 δ δ := by
    calc
      _ ≤ ∑ n ∈ range k,((k : ℝ)+1)^m*w n := by
        apply sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (mem_range.mp hn).le 1) m) (hw0 n)
      _ = ((k : ℝ)+1)^m*∑ n ∈ range k,w n := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hs0.sum_le_tsum _ (fun n _ => hw0 n)).trans hsum0) (by positivity)
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio hδ
  have hgeo := shifted_polynomial_geometric_summable m hr0 hr1
  have htailPoint (n : ℕ) : ((↑(n+k) : ℝ)+1)^m*w (n+k) ≤
      (((k : ℝ)+1)^m*(2 : ℝ)^δ)*(((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n) := by
    have hp : ((↑(n+k) : ℝ)+1)^m ≤ (((k : ℝ)+1)*((n : ℝ)+1))^m := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [show (0 : ℝ) ≤ (k : ℝ)*(n : ℝ) by positivity]
    have ht : w (n+k) ≤ (2 : ℝ)^δ*((2 : ℝ)^(-δ))^n :=
      (min_le_right _ _).trans (dyadic_ratio_high_bound hWp hδ.le hhigh n)
    exact (mul_le_mul hp ht (hw0 _) (by positivity)).trans_eq (by rw [mul_pow];ring)
  have htail : (∑' n : ℕ,((↑(n+k) : ℝ)+1)^m*w (n+k)) ≤
      (((k : ℝ)+1)^m*(2 : ℝ)^δ)*(∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n) := by
    rw [←tsum_mul_left]
    exact ((summable_nat_add_iff k).mpr hsum).tsum_le_tsum htailPoint (hgeo.mul_left _)
  have hklog : (k : ℝ)*Real.log 2 ≤ Real.log W := by
    simpa only [Real.log_pow] using Real.log_le_log (by positivity : (0 : ℝ)<(2 : ℝ)^k) hk
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h ⊢
    exact h
  have hlW : 0 ≤ Real.log W := Real.log_nonneg hW
  have hkb : (k : ℝ)+1 ≤ 2*(1+Real.log W) := by
    have hn : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hkp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ)+1) hkb m
  have hconstant : 0 ≤ interpolationWeightConstant 1 1 δ δ+(2 : ℝ)^δ*
      (∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n) := by
    exact add_nonneg (interpolationWeightConstant_nonneg (by norm_num) (by norm_num) hδ hδ)
      (mul_nonneg (by positivity) (tsum_nonneg (fun n => by positivity)))
  calc
    _ = (∑ n ∈ range k,((n : ℝ)+1)^m*w n)+∑' n : ℕ,((↑(n+k) : ℝ)+1)^m*w (n+k) :=
      (Summable.sum_add_tsum_nat_add k hsum).symm
    _ ≤ ((k : ℝ)+1)^m*interpolationWeightConstant 1 1 δ δ+
        (((k : ℝ)+1)^m*(2 : ℝ)^δ)*(∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n) := add_le_add hhead htail
    _ = ((k : ℝ)+1)^m*(interpolationWeightConstant 1 1 δ δ+(2 : ℝ)^δ*
        (∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n)) := by ring
    _ ≤ (2*(1+Real.log W))^m*(interpolationWeightConstant 1 1 δ δ+(2 : ℝ)^δ*
        (∑' n : ℕ,((n : ℝ)+1)^m*((2 : ℝ)^(-δ))^n)) := mul_le_mul_of_nonneg_right hkp hconstant
    _ = _ := by unfold polynomialDyadicProfileConstant;rw [mul_pow];ring

end PrimeSquares
