import PrimeSquares.GoldbachWeightedHarmonic

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachWeightedLogKernel (M a x : ℝ) : ℝ :=
  1/(x*(M-Real.log a-Real.log x)^2)

noncomputable def goldbachWeightedPrimeKernel (M a x : ℝ) : ℝ :=
  1/(Real.log x*(M-Real.log a-Real.log x)^2)

noncomputable def goldbachWeightedCountingModel (A x : ℝ) : ℝ :=
  A*x/Real.sqrt (Real.log x)

theorem goldbach_weighted_log_kernel_deriv (M a x : ℝ) (hx : 0<x)
    (hL : M-Real.log a-Real.log x≠0) :
    HasDerivAt (goldbachWeightedLogKernel M a)
      ((2-(M-Real.log a-Real.log x))/(x^2*(M-Real.log a-Real.log x)^3)) x := by
  have hl := (hasDerivAt_const x (M-Real.log a)).sub (Real.hasDerivAt_log hx.ne')
  have hd := (hasDerivAt_id x).mul (hl.pow 2)
  have hden : x*(M-Real.log a-Real.log x)^2≠0 := mul_ne_zero hx.ne' (pow_ne_zero 2 hL)
  convert (hasDerivAt_const x (1:ℝ)).div hd hden using 1
  · rfl
  · dsimp only [Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,Function.comp_apply,id_eq]
    field_simp
    ring

theorem goldbach_weighted_prime_kernel_deriv (M a x : ℝ) (hx : 1<x)
    (hL : M-Real.log a-Real.log x≠0) :
    HasDerivAt (goldbachWeightedPrimeKernel M a)
      ((2*Real.log x-(M-Real.log a-Real.log x))/
        (x*(Real.log x)^2*(M-Real.log a-Real.log x)^3)) x := by
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hl := (hasDerivAt_const x (M-Real.log a)).sub (Real.hasDerivAt_log hx0.ne')
  have hd := (Real.hasDerivAt_log hx0.ne').mul (hl.pow 2)
  have hden : Real.log x*(M-Real.log a-Real.log x)^2≠0 := mul_ne_zero hlog.ne' (pow_ne_zero 2 hL)
  convert (hasDerivAt_const x (1:ℝ)).div hd hden using 1
  · rfl
  · dsimp only [Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,Function.comp_apply,id_eq]
    field_simp
    ring

theorem goldbach_weighted_counting_model_deriv (A x : ℝ) (hx : 1<x) :
    HasDerivAt (goldbachWeightedCountingModel A)
      (A/Real.sqrt (Real.log x)-A/(2*(Real.sqrt (Real.log x))^3)) x := by
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hs : Real.sqrt (Real.log x)≠0 := (Real.sqrt_pos.mpr hlog).ne'
  have hd := (Real.hasDerivAt_sqrt hlog.ne').comp x (Real.hasDerivAt_log hx0.ne')
  convert ((hasDerivAt_const x A).mul (hasDerivAt_id x)).div hd hs using 1
  · rfl
  · dsimp only [Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,Function.comp_apply,id_eq]
    field_simp
    ring

theorem goldbach_weighted_log_kernel_sign (M a x : ℝ) (hx : 0<x)
    (hL : 2≤M-Real.log a-Real.log x) :
    0≤goldbachWeightedLogKernel M a x ∧
      (2-(M-Real.log a-Real.log x))/(x^2*(M-Real.log a-Real.log x)^3)≤0 := by
  have hL0 : 0<M-Real.log a-Real.log x := by linarith
  refine ⟨div_nonneg (by norm_num) (mul_nonneg hx.le (sq_nonneg _)),?_⟩
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg (sq_nonneg _) (pow_nonneg hL0.le 3))

theorem goldbach_weighted_prime_kernel_sign (M a x : ℝ) (hx : 1<x)
    (hL : 0<M-Real.log a-Real.log x)
    (hLlog : M-Real.log a-Real.log x≤2*Real.log x) :
    0≤goldbachWeightedPrimeKernel M a x ∧
      0≤(2*Real.log x-(M-Real.log a-Real.log x))/
        (x*(Real.log x)^2*(M-Real.log a-Real.log x)^3) := by
  have hlog : 0<Real.log x := Real.log_pos hx
  refine ⟨div_nonneg (by norm_num) (mul_nonneg hlog.le (sq_nonneg _)),?_⟩
  exact div_nonneg (by linarith) (by positivity)

theorem goldbach_weighted_counting_model_deriv_le (A x : ℝ) (hA : 0≤A) (hx : 1<x) :
    A/Real.sqrt (Real.log x)-A/(2*(Real.sqrt (Real.log x))^3)≤
      A/Real.sqrt (Real.log x) := by
  have hlog : 0<Real.log x := Real.log_pos hx
  have hh : 0≤A/(2*(Real.sqrt (Real.log x))^3) := by positivity
  linarith

theorem goldbach_weighted_kernel_log_identity (T a x : ℝ) (hT : 0<T) (ha : 0<a) (hx : 0<x) :
    goldbachWeightedLogKernel (Real.log T) a x=1/(x*(Real.log (T/(a*x)))^2) := by
  rw [Real.log_div hT.ne' (mul_ne_zero ha.ne' hx.ne'),Real.log_mul ha.ne' hx.ne']
  unfold goldbachWeightedLogKernel
  congr 2
  ring

end PrimeSquares
