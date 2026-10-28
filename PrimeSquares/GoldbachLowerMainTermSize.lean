import PrimeSquares.GoldbachLowerSmoothedSize
import PrimeSquares.GoldbachLowerProductBounds

set_option autoImplicit false
open Filter
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachMertensProductConstant (K : ℝ) : ℝ :=
  (1+K/Real.log 2)/(Real.log 2)^2

theorem goldbach_mertens_product_constant_pos (K : ℝ) (hK : 0≤K) :
    0<goldbachMertensProductConstant K := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold goldbachMertensProductConstant
  positivity

theorem goldbach_lower_log_preliminary (C L : ℝ) (hL : 5≤L) (hC : 1≤C) :
    5≤L^C ∧ Real.log (L^C+1)≤(C+1)*L := by
  have hL0 : 0<L := by linarith
  have hpow : L≤L^C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L) hC
  refine ⟨hL.trans hpow,?_⟩
  have hp : 0<L^C := Real.rpow_pos_of_pos hL0 C
  have hh := Real.log_le_log (by linarith : 0<L^C+1)
    (show L^C+1≤2*(L^C) by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne',Real.log_rpow hL0] at hh
  have hlog := Real.log_le_sub_one_of_pos hL0
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  nlinarith only [hh,hlog,h2,mul_le_mul_of_nonneg_left hlog (show 0≤C by linarith),hL,hC]

theorem goldbach_lower_arithmetic_logN (K C N : ℝ) (hK : 0≤K)
    (hlog : 5≤Real.log N) (hC : 1≤C) (hM : GoldbachClassicalIntervalMertens K)
    (n : ℤ) (hn : (n:ZMod 24)=12) :
    12/(goldbachMertensProductConstant K*(C+1)^2*(Real.log N)^2)≤
      (goldbachArithmeticFactor ((Real.log N)^C) 24 1 11 n).re := by
  have hL := goldbach_mertens_product_constant_pos K hK
  obtain ⟨hR,hlogR⟩ := goldbach_lower_log_preliminary C (Real.log N) hlog hC
  have hrlog : 0<Real.log ((Real.log N)^C+1) := Real.log_pos (by linarith)
  have hden : 0<(1+K/Real.log 2)*(Real.log ((Real.log N)^C+1)/Real.log 2)^2 := by
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  have he : (1+K/Real.log 2)*(Real.log ((Real.log N)^C+1)/Real.log 2)^2=
      goldbachMertensProductConstant K*(Real.log ((Real.log N)^C+1))^2 := by
    unfold goldbachMertensProductConstant
    ring
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hrlog.le hlogR 2) hL.le
  have hmono : (1+K/Real.log 2)*(Real.log ((Real.log N)^C+1)/Real.log 2)^2≤
      goldbachMertensProductConstant K*(C+1)^2*(Real.log N)^2 := by
    rw [he]
    convert hh using 1; ring
  exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤12) hden hmono).trans
    (goldbach_lower_arithmetic_polylog K ((Real.log N)^C) hK hR hM n hn)

theorem goldbach_lower_theta_logN (K R N : ℝ) (hN : 1<N)
    (hz : 2<goldbachLowerSiftingLimit N) (hK : 0≤K)
    (hM : GoldbachClassicalIntervalMertens K) (n : ℕ) :
    1/(goldbachMertensProductConstant K*(Real.log N)^2)≤
      goldbachLowerTheta R (goldbachLowerSiftingLimit N) n := by
  have hL := goldbach_mertens_product_constant_pos K hK
  have hlog : 0<Real.log N := Real.log_pos hN
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hzlog : 0<Real.log (goldbachLowerSiftingLimit N) := Real.log_pos (by linarith)
  have he : Real.log (goldbachLowerSiftingLimit N)=((8:ℝ)/9)*Real.log N := by
    exact Real.log_rpow (by linarith) _
  have hlogle : Real.log (goldbachLowerSiftingLimit N)≤Real.log N := by rw [he];linarith
  have hb := goldbach_lower_theta_inverse K R (goldbachLowerSiftingLimit N) hz hM n
  have hmono : (1+K/Real.log 2)*(Real.log (goldbachLowerSiftingLimit N)/Real.log 2)^2≤
      goldbachMertensProductConstant K*(Real.log N)^2 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hzlog.le hlogle 2) hL.le
    dsimp only [goldbachMertensProductConstant] at hh ⊢
    convert hh using 1; ring
  have hpos := goldbach_lower_theta_positive R (goldbachLowerSiftingLimit N) n
  apply (div_le_iff₀ (mul_pos hL (sq_pos_of_pos hlog))).mpr
  have hh := (inv_le_iff_one_le_mul₀ hpos).mp (hb.trans hmono)
  nlinarith only [hh]

theorem goldbach_lower_main_term_real (ψ : SchwartzMap ℝ ℝ) (N n : ℕ) (R : ℝ)
    (hR : 3≤R) (hn : (n:ZMod 24)=12) :
    goldbachLowerMainTerm ψ N R n=
      (goldbachArithmeticFactor R 24 1 11 n).re/8*
        (goldbachSingularIntegral ψ N 1 R n (N:ℝ) ((N:ℝ)^2)).re := by
  have hG := (goldbach_lower_base_real_positive R hR (n:ℤ)
    (by simpa only [Int.cast_natCast] using hn)).2
  unfold goldbachLowerMainTerm
  rw [show Nat.totient 24=8 by decide]
  norm_num [Complex.div_re,Complex.mul_re,hG]

theorem goldbach_lower_main_term_size (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (A K : ℝ) (hA : 0<A) (hK : 0≤K) (hM : GoldbachClassicalIntervalMertens K) :
    0<A/2+6 ∧ ∀ C : ℝ,A+6≤C→∃ k : ℝ,0<k ∧ ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ,(n:ZMod 24)=12→(N:ℝ)^2*(Real.log N)^(-A)≤n→n<N^2→
        k*(N:ℝ)*(Real.log N)^(-(A/2+6))≤
          goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
            goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n := by
  classical
  refine ⟨by linarith,?_⟩
  intro C hC
  let L := goldbachMertensProductConstant K
  let k := 3/(32*L^2*(C+1)^2)
  have hL : 0<L := goldbach_mertens_product_constant_pos K hK
  have hC1 : 1≤C := by linarith
  have hk : 0<k := by dsimp only [k];positivity
  refine ⟨k,hk,?_⟩
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [goldbach_lower_smoothed_size ψ hψ A,
    (Real.tendsto_log_atTop.comp hNat).eventually_ge_atTop 5,
    hNat.eventually (goldbach_lower_sieve_levels_eventually 0 1),eventually_ge_atTop 2]
    with N hSmooth hlog hLevels hN
  intro n hn hret hnN
  change 5≤Real.log (N:ℝ) at hlog
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog0 : 0<Real.log N := by linarith
  have hR : 5≤(Real.log N)^C := (goldbach_lower_log_preliminary C (Real.log N) hlog hC1).1
  have hz : 2<goldbachLowerSiftingLimit N := by
    have hh := hLevels.2.1
    rw [Real.rpow_one] at hh
    exact (show (2:ℝ)<Real.log (N:ℝ)+1 by linarith only [hlog]).trans_le hh
  have hG := goldbach_lower_arithmetic_logN K C N hK hlog hC1 hM n
    (by simpa only [Int.cast_natCast] using hn)
  have hH := hSmooth C hC n hret hnN
  have hT := goldbach_lower_theta_logN K ((Real.log N)^C) N hN1 hz hK hM n
  have hGp := (goldbach_lower_base_real_positive ((Real.log N)^C) (by linarith) (n:ℤ)
    (by simpa only [Int.cast_natCast] using hn)).1.le
  have hHp : 0≤(goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)).re :=
    le_trans (by positivity) hH
  have hGH := mul_le_mul (div_le_div_of_nonneg_right hG (by norm_num : (0:ℝ)≤8)) hH
    (by positivity : (0:ℝ)≤(N:ℝ)/(16*(Real.log N)^(A/2+2))) (by positivity : (0:ℝ)≤
      (goldbachArithmeticFactor ((Real.log N)^C) 24 1 11 n).re/8)
  have hAll := mul_le_mul hGH hT
    (by positivity : (0:ℝ)≤1/(L*(Real.log N)^2)) (mul_nonneg (by positivity) hHp)
  rw [←goldbach_lower_main_term_real ψ N n ((Real.log N)^C) (by linarith) hn] at hAll
  apply le_trans _ hAll
  dsimp only [k,L]
  rw [Real.rpow_neg hlog0.le,show A/2+6=(A/2+2)+2+2 by ring,
    Real.rpow_add hlog0,Real.rpow_add hlog0,Real.rpow_two]
  field_simp
  norm_num

end PrimeSquares
