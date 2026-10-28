import PrimeSquares.GoldbachLowerSmoothedSize

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_weighted_smoothing_relative (a C K N L H : ℝ)
    (hL : 1≤L) (hC : a+6≤C) (hK : 0≤K) (hN : 0≤N)
    (hH : N/(8*L^(a/2+2))≤H) :
    K*N/Real.sqrt (L^C)≤(8*K/L)*H := by
  have hL0 : 0<L := by linarith
  have hsqrt : Real.sqrt (L^C)=L^(C/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hL0.le]
    congr 1
    ring
  have hden : L^(a/2+3)≤L^(C/2) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hh := div_le_div_of_nonneg_left (mul_nonneg hK hN)
    (Real.rpow_pos_of_pos hL0 _) hden
  have hpow : L^(a/2+3)=L^(a/2+2)*L := by
    rw [show a/2+3=(a/2+2)+1 by ring,Real.rpow_add hL0,Real.rpow_one]
  have he : K*N/L^(a/2+3)=(8*K/L)*(N/(8*L^(a/2+2))) := by rw [hpow];ring
  rw [hsqrt]
  exact hh.trans (he.trans_le (mul_le_mul_of_nonneg_left hH (by positivity)))

theorem goldbach_weighted_reference_lower_scalar (a L q N density H : ℝ)
    (hL : 1≤L) (hq : 1≤q) (hN : 0≤N) (hd : 0≤density)
    (hH : N/(8*L^(a/2+2))≤H) :
    density*N/(8*L^(a/2+3))≤density*H*Real.sqrt q/Real.sqrt L := by
  have hL0 : 0<L := by linarith
  have hs : 0<Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsL : Real.sqrt L≤L := Real.sqrt_le_iff.mpr ⟨hL0.le,by nlinarith⟩
  have hsq : 1≤Real.sqrt q := by
    have hh := Real.sqrt_le_sqrt hq
    simpa only [Real.sqrt_one] using hh
  have hr : 1/L≤Real.sqrt q/Real.sqrt L := by
    apply (div_le_div_iff₀ hL0 hs).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsq hL0.le,hsL]
  have hH0 : 0≤H := (by positivity : 0≤N/(8*L^(a/2+2))).trans hH
  have hh := mul_le_mul hH hr (by positivity : 0≤1/L) hH0
  have hh' := mul_le_mul_of_nonneg_left hh hd
  have hpow : L^(a/2+3)=L^(a/2+2)*L := by
    rw [show a/2+3=(a/2+2)+1 by ring,Real.rpow_add hL0,Real.rpow_one]
  rw [hpow]
  convert hh' using 1 <;> ring

theorem goldbach_weighted_thin_ratio_scalar (a N L root : ℝ)
    (hL : 1≤L) (hN : 0<N) (hroot : N/L^(a/2)≤root) :
    2*(N^2*L^(-(a+14)))/root≤2*N/L^(a/2+14) := by
  have hL0 : 0<L := by linarith
  have hh := div_le_div_of_nonneg_left (by positivity : 0≤2*(N^2*L^(-(a+14))))
    (div_pos hN (Real.rpow_pos_of_pos hL0 _)) hroot
  apply hh.trans_eq
  rw [Real.rpow_neg hL0.le,←div_eq_mul_inv]
  have hp : L^(a+14)=L^(a/2+14)*L^(a/2) := by rw [←Real.rpow_add hL0];congr 1;ring
  rw [hp]
  field_simp

theorem goldbach_weighted_thin_error_relative (a N L root density base q f mass M S : ℝ)
    (hL : 1≤L) (hN : 0<N) (hroot : N/L^(a/2)≤root)
    (hd : 0≤density) (_hb : 0≤base) (hbd : base≤density)
    (hq : 0≤q) (hqL : q≤L) (hf : 0≤f) (hf2 : f≤2)
    (hmass : 0≤mass) (hM : 0≤M) (hmassM : mass≤M*L^7)
    (hS : density*N/(8*L^(a/2+3))≤S) :
    (24*base*f*q)*((2*(N^2*L^(-(a+14)))/root)*mass/(Real.log 2)^3)≤
      ((768*M/(Real.log 2)^3)/L^3)*S := by
  have hL0 : 0<L := by linarith
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hroot0 : 0<root := (div_pos hN (Real.rpow_pos_of_pos hL0 _)).trans_le hroot
  have ht := goldbach_weighted_thin_ratio_scalar a N L root hL hN hroot
  have htmass := div_le_div_of_nonneg_right
    (mul_le_mul ht hmassM hmass (by positivity)) (by positivity : 0≤(Real.log 2)^3)
  have hcoeff : 24*base*f*q≤24*density*2*L := by
    have hh := mul_le_mul (mul_le_mul hbd hf2 hf hd) hqL hq (by positivity)
    nlinarith only [hh]
  have hprod := mul_le_mul hcoeff htmass (by positivity) (by positivity)
  have hrel := mul_le_mul_of_nonneg_left hS
    (show 0≤(768*M/(Real.log 2)^3)/L^3 by positivity)
  apply hprod.trans
  apply le_trans _ hrel
  apply le_of_eq
  have hp : L^(a/2+14)=L^(a/2+3)*L^11 := by
    rw [←Real.rpow_natCast,←Real.rpow_add hL0]
    congr 1
    norm_num
    ring
  rw [hp]
  field_simp
  ring

theorem goldbach_weighted_smooth_error_relative (a C N L density base K mass M S : ℝ)
    (hL : 1≤L) (hC : a+24≤C) (hN : 0≤N)
    (hd : 0≤density) (_hb : 0≤base) (hbd : base≤density) (hK : 0≤K)
    (hmass : 0≤mass) (hM : 0≤M) (hmassM : mass≤M*L^7)
    (hS : density*N/(8*L^(a/2+3))≤S) :
    6*base*(K*N/Real.sqrt (L^C))*mass≤((48*M*K)/L^2)*S := by
  have hL0 : 0<L := by linarith
  have hsqrt : Real.sqrt (L^C)=L^(C/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hL0.le]
    congr 1
    ring
  have hden : L^(a/2+12)≤L^(C/2) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hsm := div_le_div_of_nonneg_left (mul_nonneg hK hN) (Real.rpow_pos_of_pos hL0 _) hden
  rw [←hsqrt] at hsm
  have hprod := mul_le_mul (mul_le_mul hbd hsm (by positivity) hd) hmassM hmass (by positivity)
  have hprod' := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ)≤6)
  have hrel := mul_le_mul_of_nonneg_left hS (show 0≤(48*M*K)/L^2 by positivity)
  have heq : 6*(density*(K*N/L^(a/2+12))*(M*L^7))=
      ((48*M*K)/L^2)*(density*N/(8*L^(a/2+3))) := by
    have hp : L^(a/2+12)=L^(a/2+3)*L^9 := by
      rw [←Real.rpow_natCast,←Real.rpow_add hL0]
      congr 1
      norm_num
      ring
    rw [hp]
    field_simp
    ring
  have hp0 : 6*base*(K*N/Real.sqrt (L^C))*mass≤6*(density*(K*N/L^(a/2+12))*(M*L^7)) := by
    convert hprod' using 1;ring
  exact hp0.trans (heq.trans_le hrel)

theorem goldbach_weighted_error_coefficient_limit (M K : ℝ) :
    Tendsto (fun L : ℝ=>(768*M/(Real.log 2)^3)/L^3+(48*M*K)/L^2) atTop (nhds 0) := by
  have hInv : Tendsto (fun L : ℝ=>1/L) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hh := ((hInv.pow 3).const_mul (768*M/(Real.log 2)^3)).add ((hInv.pow 2).const_mul (48*M*K))
  simpa [div_pow,div_eq_mul_inv] using hh

theorem goldbach_weighted_thin_cutoff (a N L n : ℝ) (hL : 2≤L) (_hN : 0≤N)
    (hret : N^2*L^(-a)≤n) : N^2*L^(-(a+14))≤n/4 := by
  have hL0 : 0<L := by linarith
  have hp : (4:ℝ)≤L^14 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hL 14
    norm_num at hh
    linarith
  have he : (N^2*L^(-(a+14)))*L^14=N^2*L^(-a) := by
    rw [show -(a+14)=-a+(-14) by ring,Real.rpow_add hL0]
    simp only [Real.rpow_neg hL0.le,Real.rpow_ofNat]
    have hLp : L^14≠0 := pow_ne_zero _ hL0.ne'
    field_simp
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0≤N^2*L^(-(a+14)))
  rw [he] at hh
  linarith

end PrimeSquares
