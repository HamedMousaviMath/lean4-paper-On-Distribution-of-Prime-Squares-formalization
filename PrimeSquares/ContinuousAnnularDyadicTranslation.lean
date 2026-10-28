import PrimeSquares.ContinuousAnnularFarTranslation
import PrimeSquares.DyadicAbsoluteProfile

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem dyadic_annular_translation_ratio (j : ℕ) (H : ℝ) :
    (((2 : ℕ)^(j+1) : ℕ) : ℝ)^2/H=(4 : ℝ)^j*(4/H) := by
  push_cast
  rw [←pow_mul,mul_comm (j+1) 2,pow_mul]
  norm_num
  rw [pow_succ]
  ring

theorem annularFarTranslation_dyadic_sum {β : ℝ} (hβ0 : 0≤β) (hβ1 : β≤1)
    (h : ℝ) (J : ℕ) :
    (∑ j∈range J,∫ x,annularFarTranslation ((2 : ℕ)^(j+1)) β h x)≤70/3 := by
  by_cases hz : h=0
  · subst h
    norm_num [annularFarTranslation]
  · have hh : 0 < |h| := abs_pos.mpr hz
    calc
      _ ≤ ∑ j∈range J,7*min ((4 : ℝ)^j*(4/|h|)) (((4 : ℝ)^j*(4/|h|))⁻¹) := by
        apply sum_le_sum
        intro j _
        have hN : 2≤(2 : ℕ)^(j+1) := by
          have hpos := one_le_pow₀ (by norm_num : 1≤(2 : ℕ)) (n := j)
          rw [pow_succ]
          omega
        simpa only [dyadic_annular_translation_ratio] using
          annularFarTranslation_profile hN hβ0 hβ1 hh
      _ = 7*(∑ j∈range J,min ((4 : ℝ)^j*(4/|h|)) (((4 : ℝ)^j*(4/|h|))⁻¹)) := by
        rw [mul_sum]
      _ ≤ 7*(10/3 : ℝ) := mul_le_mul_of_nonneg_left
        (dyadic_absolute_profile_sum (by positivity : 0≤4/|h|) J) (by norm_num)
      _ = _ := by ring

theorem annularFarTranslation_all_dyadic_sum {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (h : ℝ) (J : ℕ) :
    (∑ j∈range J,∫ x,annularFarTranslation ((2 : ℕ)^j) β h x)≤2+70/3 := by
  cases J with
  | zero => norm_num
  | succ J =>
    rw [sum_range_succ']
    have hfirst : (∫ x,annularFarTranslation 1 β h x)≤2 :=
      (annularFarTranslation_integral_le (by norm_num) β h).trans
        (continuousAnnularKernel_translation_rough (by norm_num) hβ0 hβ1 h)
    simpa only [pow_zero,add_comm (70/3 : ℝ) 2] using add_le_add
      (annularFarTranslation_dyadic_sum hβ0.le hβ1 h J) hfirst

end PrimeSquares
