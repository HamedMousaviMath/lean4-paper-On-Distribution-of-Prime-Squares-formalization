import PrimeSquares.DyadicAbsoluteProfile
import PrimeSquares.SourceArcCutoff

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem sourceCutoff_difference_abs_le_one (x y : ℝ) :
    |sourceArcCutoff x-sourceArcCutoff y|≤1 := by
  apply abs_le.mpr
  constructor <;> linarith [sourceArcCutoff_nonneg x,sourceArcCutoff_nonneg y,
    sourceArcCutoff_le_one x,sourceArcCutoff_le_one y]

theorem sourceCutoff_dilation_near (x : ℝ) :
    |sourceArcCutoff (4*x)-sourceArcCutoff x|≤8*|x| := by
  by_cases hx : |x|≤1/8
  · have h4 : sourceArcCutoff (4*x)=1 := by
      apply sourceArcCutoff_core
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)]
      linarith
    have h1 : sourceArcCutoff x=1 := sourceArcCutoff_core (by linarith)
    rw [h4,h1,sub_self,abs_zero]
    positivity
  · have h := sourceCutoff_difference_abs_le_one (4*x) x
    linarith

theorem sourceCutoff_dilation_far (x : ℝ) :
    |x| * |sourceArcCutoff (4*x)-sourceArcCutoff x|≤1 := by
  by_cases hx : 1≤|x|
  · have h4 : sourceArcCutoff (4*x)=0 := by
      apply sourceArcCutoff_zero
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)]
      linarith
    rw [h4,sourceArcCutoff_zero hx,sub_self,abs_zero,mul_zero]
    norm_num
  · have he := sourceCutoff_difference_abs_le_one (4*x) x
    exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans
      (by simpa only [mul_one] using (le_of_lt (lt_of_not_ge hx)))

theorem sourceCutoff_dilation_profile (x : ℝ) :
    |sourceArcCutoff (4*x)-sourceArcCutoff x|≤8*min |x| (|x|⁻¹) :=
  two_sided_absolute_profile (abs_nonneg _) (sourceCutoff_dilation_near x)
    ((sourceCutoff_dilation_far x).trans (by norm_num))

theorem sourceCutoff_dyadic_variation (x : ℝ) (J : ℕ) :
    (∑ j∈range J,|sourceArcCutoff ((4 : ℝ)^(j+1)*x)-sourceArcCutoff ((4 : ℝ)^j*x)|)≤80/3 := by
  calc
    _ ≤ ∑ j∈range J,(8 : ℝ)*min ((4 : ℝ)^j*|x|) (((4 : ℝ)^j*|x|)⁻¹) := by
      apply sum_le_sum
      intro j _
      have h := sourceCutoff_dilation_profile ((4 : ℝ)^j*x)
      simpa only [pow_succ,show (4 : ℝ)^j*4*x=4*((4 : ℝ)^j*x) by ring,
        abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤4^j)] using h
    _ = 8*∑ j∈range J,min ((4 : ℝ)^j*|x|) (((4 : ℝ)^j*|x|)⁻¹) := (mul_sum _ _ _).symm
    _ ≤ 8*(10/3 : ℝ) := mul_le_mul_of_nonneg_left (dyadic_absolute_profile_sum (abs_nonneg _) J) (by norm_num)
    _ = _ := by norm_num

end PrimeSquares
