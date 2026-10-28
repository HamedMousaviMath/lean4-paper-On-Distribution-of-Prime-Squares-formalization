import PrimeSquares.GoldbachUpperSieveRemainder
import PrimeSquares.GoldbachFixedSieveSets

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

noncomputable def goldbachUpperFinalError (ψ : SchwartzMap ℝ ℝ) (N : ℕ)
    (B R K : ℝ) (c : ℕ→ℕ→ℝ) (n : ℕ) : ℝ :=
  goldbachUpperRemainderSum ψ N B R c n+K*(N:ℝ)^(1/4:ℝ)

theorem goldbach_upper_error_square_sum (ψ : SchwartzMap ℝ ℝ) (N : ℕ) (hN : 4≤N)
    (B R M A K : ℝ) (hlog : (Real.log N)^A≤N)
    (c : ℕ→ℕ→ℝ) (hrem : (∑ n∈range (N^2),(goldbachUpperRemainderSum ψ N B R c n)^2)≤
      (2*M)*(N:ℝ)^4*(Real.log N)^(-A)) :
    (∑ n∈range (N^2),(goldbachUpperFinalError ψ N B R K c n)^2)≤
      (4*M+2*K^2)*(N:ℝ)^4*(Real.log N)^(-A) := by
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hN0 : (0:ℝ)<N := by linarith
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hq : ((N:ℝ)^(1/4:ℝ))^2≤N := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat,show (1/4:ℝ)*2=1/2 by norm_num]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/2:ℝ)≤1)
  have hpoint (n : ℕ) : (goldbachUpperFinalError ψ N B R K c n)^2≤
      2*(goldbachUpperRemainderSum ψ N B R c n)^2+2*K^2*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hq (sq_nonneg K)
    have hs := sq_nonneg (goldbachUpperRemainderSum ψ N B R c n-K*(N:ℝ)^(1/4:ℝ))
    unfold goldbachUpperFinalError
    nlinarith only [hh,hs]
  have hcubic : (N:ℝ)^3≤(N:ℝ)^4*(Real.log N)^(-A) := by
    rw [Real.rpow_neg hL.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog (pow_nonneg hN0.le 3)
    convert hh using 1;ring
  calc
    _≤∑ n∈range (N^2),(2*(goldbachUpperRemainderSum ψ N B R c n)^2+2*K^2*(N:ℝ)) :=
      sum_le_sum (fun n _=>hpoint n)
    _=2*(∑ n∈range (N^2),(goldbachUpperRemainderSum ψ N B R c n)^2)+2*K^2*(N:ℝ)^3 := by
      rw [sum_add_distrib,←mul_sum]
      simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_pow]
      ring
    _≤2*((2*M)*(N:ℝ)^4*(Real.log N)^(-A))+2*K^2*((N:ℝ)^4*(Real.log N)^(-A)) :=
      add_le_add (mul_le_mul_of_nonneg_left hrem (by norm_num))
        (mul_le_mul_of_nonneg_left hcubic (by positivity))
    _=_ := by ring

theorem goldbach_upper_arithmetic_error_eventually (A : ℝ) :
    ∀ᶠ N : ℕ in atTop,(Real.log N)^A≤N := by
  have hh := eventually_log_rpow_le_rpow A (by norm_num : (0:ℝ)<1)
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_one] using hNat.eventually hh

end PrimeSquares
