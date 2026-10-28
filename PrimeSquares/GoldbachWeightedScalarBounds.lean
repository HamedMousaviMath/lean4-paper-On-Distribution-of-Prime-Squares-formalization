import PrimeSquares.GoldbachWeightedFiniteKernel

set_option autoImplicit false
namespace PrimeSquares

theorem goldbach_weighted_prime_reciprocal_coarse (L K : ℝ) (hL : 1≤L)
    (hK : K≤L) : (L+K)/((4/9:ℝ)*(2*L))≤3 := by
  apply (div_le_iff₀ (by positivity : 0<(4/9:ℝ)*(2*L))).mpr
  linarith

theorem goldbach_weighted_small_scalar (L H K : ℝ) (hL : 1≤L) (hH : 0≤H) (hK : K≤L) :
    H*(((2*L)/2+K)/((4/9:ℝ)*(2*L)))/(2*((4/9:ℝ)*(2*L))^2)≤2*H/L^2 := by
  have hL0 : 0<L := by linarith
  have hq := goldbach_weighted_prime_reciprocal_coarse L K hL hK
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq hH)
    (show 0≤2*((4/9:ℝ)*(2*L))^2 by positivity)
  have hn : H*3/(2*((4/9:ℝ)*(2*L))^2)≤2*H/L^2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hL0)).mpr
    have hpos := mul_nonneg hH (sq_nonneg L)
    nlinarith only [hpos]
  have he : (2*L)/2=L := by ring
  rw [he]
  exact hh.trans hn

theorem goldbach_weighted_sharp_scalar_identity (L A F W : ℝ) (hL : 0<L) :
    (1/2:ℝ)*(A/(2*(2*L)^2)*F*Real.sqrt (2*L)*(8*Real.sqrt 2*W))=
      A*F*W/(L*Real.sqrt L) := by
  have hsL : Real.sqrt L≠0 := (Real.sqrt_pos.mpr hL).ne'
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  field_simp
  rw [Real.sq_sqrt hL.le,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  ring

theorem goldbach_weighted_large_scalar (L a A K : ℝ) (hL : 9≤L) (ha : 2≤a)
    (haU : a≤Real.exp ((2*L)/9)/2) (hA : 0≤A) (hK : 0≤K) (hKL : K≤L)
    (hexp : L≤Real.exp ((8/9:ℝ)*L)) :
    (1/2:ℝ)*((A/(2*(2*L)^2))*Real.sqrt (1+Real.log 2/Real.log a)*Real.sqrt (2*L)*
      (8*Real.sqrt 2*goldbachWeightedW (9/8))+
      A*goldbachWeightedPrimeError (2*L) K*
        ((Real.log (Real.exp ((2*L)/9)/2)-Real.log a)/Real.sqrt (Real.log a))+
      A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)*(((2*L)/2+K)/((4/9:ℝ)*(2*L))))≤
      A*Real.sqrt (1+Real.log 2/Real.log a)*goldbachWeightedW (9/8)/(L*Real.sqrt L)+
        6*(K+1)*A/(Real.sqrt (Real.log a)*L^2) := by
  have hL0 : 0<L := by linarith
  have hloga : 0<Real.log a := Real.log_pos (by linarith)
  have hs : 0<Real.sqrt (Real.log a) := Real.sqrt_pos.mpr hloga
  have hU0 : 0<Real.exp ((2*L)/9)/2 := by positivity
  have hlogdiff0 : 0≤Real.log (Real.exp ((2*L)/9)/2)-Real.log a :=
    sub_nonneg.mpr (Real.log_le_log (by linarith : 0<a) haU)
  have hlogdiff : Real.log (Real.exp ((2*L)/9)/2)-Real.log a≤L := by
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
    have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have he := goldbach_weighted_prime_error_coarse L K (by linarith) hK hexp
  have hq := goldbach_weighted_prime_reciprocal_coarse L K (by linarith) hKL
  have hE0 : 0≤goldbachWeightedPrimeError (2*L) K := by
    dsimp only [goldbachWeightedPrimeError]
    positivity
  have hp := mul_le_mul he hlogdiff hlogdiff0
    (by positivity : 0≤8*(K+1)/L^3)
  have hErr : (1/2:ℝ)*(A*goldbachWeightedPrimeError (2*L) K*
      ((Real.log (Real.exp ((2*L)/9)/2)-Real.log a)/Real.sqrt (Real.log a)))≤
        4*(K+1)*A/(Real.sqrt (Real.log a)*L^2) := by
    have hh := mul_le_mul_of_nonneg_left hp
      (div_nonneg hA (show 0≤2*Real.sqrt (Real.log a) by positivity))
    convert hh using 1 <;> field_simp; ring
  have hBdy : (1/2:ℝ)*(A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)*
      (((2*L)/2+K)/((4/9:ℝ)*(2*L))))≤2*A/(Real.sqrt (Real.log a)*L^2) := by
    have hh := mul_le_mul_of_nonneg_left hq
      (show 0≤(1/2:ℝ)*(A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)) by positivity)
    have hnum : ((1/2:ℝ)*(A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)))*3≤
        2*A/(Real.sqrt (Real.log a)*L^2) := by
      apply (le_div_iff₀ (mul_pos hs (sq_pos_of_pos hL0))).mpr
      have heq : ((1/2:ℝ)*(A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)))*3*
          (Real.sqrt (Real.log a)*L^2)=(243/128:ℝ)*A := by field_simp;ring
      rw [heq]
      nlinarith only [hA]
    have hh' : (1/2:ℝ)*(A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)*
        (((2*L)/2+K)/((4/9:ℝ)*(2*L))))≤
        ((1/2:ℝ)*(A/(Real.sqrt (Real.log a)*((4/9:ℝ)*(2*L))^2)))*3 := by
      convert hh using 1;ring
    exact hh'.trans hnum
  have hmain := goldbach_weighted_sharp_scalar_identity L A
    (Real.sqrt (1+Real.log 2/Real.log a)) (goldbachWeightedW (9/8)) hL0
  have hfinal : 4*(K+1)*A/(Real.sqrt (Real.log a)*L^2)+2*A/(Real.sqrt (Real.log a)*L^2)≤
      6*(K+1)*A/(Real.sqrt (Real.log a)*L^2) := by
    rw [←add_div]
    apply (div_le_div_iff_of_pos_right (mul_pos hs (sq_pos_of_pos hL0))).mpr
    nlinarith only [mul_nonneg hK hA]
  nlinarith only [hErr,hBdy,hmain,hfinal]

end PrimeSquares
