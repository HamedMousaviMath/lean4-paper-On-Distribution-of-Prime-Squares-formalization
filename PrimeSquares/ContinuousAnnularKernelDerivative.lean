import PrimeSquares.ContinuousAnnularKernel

set_option autoImplicit false
namespace PrimeSquares

noncomputable def annularKernelDerivative (N : ℕ) (β x : ℝ) : ℝ :=
  (β/2-1)*x^(β/2-2)/(2*(N : ℝ))

theorem annularKernelDensity_hasDerivAt (N : ℕ) (β : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (annularKernelDensity N β) (annularKernelDerivative N β x) x := by
  unfold annularKernelDensity annularKernelDerivative
  have he : (β/2-1)-1=β/2-2 := by ring
  simpa only [he] using (Real.hasDerivAt_rpow_const (x := x) (p := β/2-1) (Or.inl hx.ne')).div_const
    (2*(N : ℝ))

theorem annularKernelDerivative_density (N : ℕ) (β : ℝ) {x : ℝ} (hx : 0<x) :
    annularKernelDerivative N β x=(β/2-1)*annularKernelDensity N β x/x := by
  have hp : x^(β/2-2)=x^(β/2-1)/x := by
    calc
      _ = x^((β/2-1)-1) := by congr 1;ring
      _ = _ := by rw [Real.rpow_sub hx,Real.rpow_one]
  unfold annularKernelDerivative annularKernelDensity
  rw [hp]
  ring

theorem annularKernelDerivative_bound {N : ℕ} (hN : 2≤N) {β x : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1) (hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) :
    |annularKernelDerivative N β x|≤4/(N : ℝ)^4 := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hxp : 0<x := (by positivity : (0 : ℝ)<(N : ℝ)^2/4).trans_le hx.1
  have hc : |β/2-1|≤1 := by
    rw [abs_of_nonpos (by linarith : β/2-1≤0)]
    linarith
  have hd0 : 0≤annularKernelDensity N β x := by
    unfold annularKernelDensity
    positivity
  have hd := annularKernelDensity_bound hN hβ1 hx
  have hi : 1/x≤4/(N : ℝ)^2 := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<(N : ℝ)^2/4) hx.1
    exact h.trans_eq (by ring)
  rw [annularKernelDerivative_density N β hxp,abs_div,abs_mul,abs_of_nonneg hd0,abs_of_pos hxp,
    div_eq_mul_one_div]
  calc
    _ ≤ (1*(1/(N : ℝ)^2))*(4/(N : ℝ)^2) :=
      mul_le_mul (mul_le_mul hc hd hd0 (by norm_num)) hi (by positivity) (by positivity)
    _ = _ := by ring

end PrimeSquares
