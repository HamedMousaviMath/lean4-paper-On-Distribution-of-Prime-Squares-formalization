import PrimeSquares.OrliczScaleComparison
import PrimeSquares.PrimeStoppingLocalEndpoint

set_option autoImplicit false
open Finset
namespace PrimeSquares

def enlargedStoppingParent (I : SparseIntegerInterval) (m : ℕ) (hm : 1 ≤ m) : SparseIntegerInterval where
  left := I.left
  length := m*I.length
  length_pos := Nat.mul_pos (by omega) I.length_pos

theorem enlargedStoppingParent_contains (I : SparseIntegerInterval) (m : ℕ) (hm : 1 ≤ m) :
    I.points ⊆ (enlargedStoppingParent I m hm).points := by
  intro x hx
  rw [integerInterval_mem_points] at hx ⊢
  simp only [enlargedStoppingParent,Nat.cast_mul]
  have hL : (0:ℤ)<I.length := by exact_mod_cast I.length_pos
  have hm' : (1:ℤ)≤m := by exact_mod_cast hm
  constructor
  · exact hx.1
  · nlinarith

theorem enlargedStoppingParent_support (I : SparseIntegerInterval) (m : ℕ) (hm : 1 ≤ m)
    (F : Finset ℤ) (hF : ∀ y ∈ F,|y-I.left| ≤ (m:ℤ)*I.length) :
    F ⊆ (enlargedStoppingParent I m hm).five.points := by
  intro y hy
  rw [integerInterval_mem_points]
  simp only [enlargedStoppingParent,SparseIntegerInterval.five,Nat.cast_mul,Nat.cast_ofNat]
  have hh := (abs_le.mp (hF y hy))
  have hp : (0:ℤ)<(m:ℤ)*I.length := by exact_mod_cast Nat.mul_pos (by omega : 0<m) I.length_pos
  constructor <;> nlinarith

theorem paperPhi_half_minimum {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    paperPhi c (1/2) 1 ≤ paperPhi c (1/2) b := by
  have hL : paperLog 1 ≤ paperLog b := by
    simpa only [paperLog,Real.log_one,abs_zero,add_zero] using paperLog_two_le b
  have hw := orliczWeight_half_mono (paperLog_two_le 1) hL
  rw [paperPhi_eq_exp_weight,paperPhi_eq_exp_weight]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hc)

theorem paperPhi_half_fixed_rescale_all {c a b K : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (ha1 : a ≤ 1) (hK : 1 ≤ K) (hab : a ≤ b) (hba : b ≤ K*a) :
    paperPhi c (1/2) a ≤ Real.exp (c*Real.sqrt (Real.log K)/2)*paperPhi c (1/2) b := by
  by_cases hb : b ≤ 1
  · exact paperPhi_half_fixed_rescale hc ha hb hK hab hba
  · have h1 : 1 ≤ K*a := by linarith
    exact (paperPhi_half_fixed_rescale hc ha (by norm_num) hK ha1 h1).trans
      (mul_le_mul_of_nonneg_left (paperPhi_half_minimum hc b) (Real.exp_pos _).le)

theorem primeEndpoint_fixed_density_rescale {c a b K : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (ha1 : a ≤ 1) (hK : 1 ≤ K) (hab : a ≤ b) (hba : b ≤ K*a) :
    a^(2/3:ℝ)*paperPhi c (1/2) a ≤
      Real.exp (c*Real.sqrt (Real.log K)/2)*b^(2/3:ℝ)*paperPhi c (1/2) b := by
  have hp := Real.rpow_le_rpow ha.le hab (by norm_num : (0:ℝ)≤2/3)
  have hf := paperPhi_half_fixed_rescale_all hc ha ha1 hK hab hba
  calc
    _ ≤ b^(2/3:ℝ)*(Real.exp (c*Real.sqrt (Real.log K)/2)*paperPhi c (1/2) b) :=
      mul_le_mul hp hf (paperPhi_pos _ _ _).le (Real.rpow_nonneg (ha.le.trans hab) _)
    _ = _ := by ring

theorem enlargedStoppingParent_density (I : SparseIntegerInterval) (m : ℕ) (hm : 1 ≤ m)
    (F G : Finset ℤ) : finiteSetDensity I.length F G=
      (5*(m:ℝ))^2*finiteSetDensity (5*((enlargedStoppingParent I m hm).length:ℝ)) F G := by
  have hI : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  unfold finiteSetDensity enlargedStoppingParent
  push_cast
  field_simp

end PrimeSquares
