import PrimeSquares.GoldbachArchimedeanLower
import PrimeSquares.GoldbachLowerSieveParameters

set_option autoImplicit false
open Filter
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_retained_sqrt_lower (A N n : ℝ) (hN : 1<N) (hn : 0≤n)
    (hret : N^2*(Real.log N)^(-A)≤n) :
    N/(Real.log N)^(A/2)≤Real.sqrt n := by
  have hlog := Real.log_pos hN
  have hp : ((Real.log N)^(A/2))^2=(Real.log N)^A := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hlog.le]
    congr 1
    ring
  have he : (N/(Real.log N)^(A/2))^2=N^2*(Real.log N)^(-A) := by
    rw [div_pow,hp,Real.rpow_neg hlog.le]
    rfl
  have hs := Real.sq_sqrt hn
  have hq : 0≤N/(Real.log N)^(A/2) := by positivity
  have hs0 := Real.sqrt_nonneg n
  nlinarith only [hret,he,hs,hq,hs0]

theorem goldbach_archimedean_retained_lower (A : ℝ) (N n : ℕ) (hN : 2≤N)
    (hn : 64≤n) (hnN : n≤N^2)
    (hret : (N:ℝ)^2*(Real.log N)^(-A)≤n) :
    (N:ℝ)/(8*(Real.log N)^(A/2+2))≤
      (goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re := by
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hs := goldbach_retained_sqrt_lower A N n (by exact_mod_cast (show 1<N by omega))
    (Nat.cast_nonneg _) hret
  have hb := goldbach_archimedean_lower N hN n (by exact_mod_cast hn) (by exact_mod_cast hnN)
  have hh := div_le_div_of_nonneg_right hs (by positivity : (0:ℝ)≤8*(Real.log N)^2)
  have he : ((N:ℝ)/(Real.log N)^(A/2))/(8*(Real.log N)^2)=
      (N:ℝ)/(8*(Real.log N)^(A/2+2)) := by
    rw [Real.rpow_add hlog,Real.rpow_two]
    field_simp
  exact he ▸ hh.trans hb

theorem goldbach_smoothing_error_small (A C K N L : ℝ)
    (hN : 0≤N) (hL : 1≤L) (hLK : 16*K≤L) (hC : A+6≤C) :
    K*N/Real.sqrt (L^C)≤N/(16*L^(A/2+2)) := by
  have hL0 : 0<L := by linarith
  have he : Real.sqrt (L^C)=L^(C/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hL0.le]
    congr 1
    ring
  have hden : 16*K*L^(A/2+2)≤L^(C/2) := by
    calc
      _≤L*L^(A/2+2) := mul_le_mul_of_nonneg_right hLK (Real.rpow_nonneg hL0.le _)
      _=L^(A/2+2+1) := by rw [Real.rpow_add hL0 (A/2+2) 1,Real.rpow_one];ring
      _≤_ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  rw [he]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hL0 _) (by positivity : 0<16*L^(A/2+2))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hden hN]

theorem goldbach_retained_height_eventually (A : ℝ) :
    ∀ᶠ N : ℝ in atTop,64≤N ∧ N≤N^2*(Real.log N)^(-A) := by
  filter_upwards [eventually_ge_atTop (64:ℝ),
    eventually_log_rpow_le_rpow A (by norm_num : (0:ℝ)<1)] with N hN hpow
  have hlog := Real.log_pos (show 1<N by linarith)
  have hp := Real.rpow_pos_of_pos hlog A
  refine ⟨hN,?_⟩
  rw [Real.rpow_neg hlog.le,←div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  have hh : (Real.log N)^A≤N := by simpa only [Real.rpow_one] using hpow
  nlinarith only [mul_le_mul_of_nonneg_left hh (show 0≤N by linarith)]

theorem goldbach_lower_smoothed_size (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ C : ℝ,A+6≤C→∀ n : ℕ,
      (N:ℝ)^2*(Real.log N)^(-A)≤n→n<N^2→
      (N:ℝ)/(16*(Real.log N)^(A/2+2))≤
        (goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)).re := by
  obtain ⟨K,hK,hSmooth⟩ := goldbach_positive_singular_integral_complete ψ hψ
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLog := Real.tendsto_log_atTop.comp hNat
  filter_upwards [hNat.eventually (goldbach_retained_height_eventually A),
    hLog.eventually_ge_atTop (max 1 (16*K))] with N hHeight hLogN
  intro C hC n hret hnN
  have hNr : (64:ℝ)≤N := hHeight.1
  have hN : 2≤N := by exact_mod_cast (show (2:ℝ)≤N by linarith)
  have hn : 64≤n := by exact_mod_cast hHeight.1.trans (hHeight.2.trans hret)
  have hlog : 0<Real.log N := Real.log_pos (by linarith)
  have hR := Real.rpow_pos_of_pos hlog C
  have hb := goldbach_archimedean_retained_lower A N n hN hn (by omega) hret
  have hs := (hSmooth N 1 (by omega) (by decide) ((Real.log N)^C) N ((N:ℝ)^2) n
    hR (by exact_mod_cast hN) le_rfl (by nlinarith) (by exact_mod_cast hnN)).2.2
  have he := goldbach_smoothing_error_small A C K N (Real.log N) (Nat.cast_nonneg _)
    ((le_max_left _ _).trans hLogN) ((le_max_right _ _).trans hLogN) hC
  have hr := Complex.abs_re_le_norm
    (goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)-
      goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2))
  have hneg := neg_abs_le
    ((goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)-
      goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re)
  simp only [Complex.sub_re] at hr hneg
  have hq : 0<(Real.log N)^(A/2+2) := Real.rpow_pos_of_pos hlog _
  have heq : (N:ℝ)/(8*(Real.log N)^(A/2+2))=
      2*((N:ℝ)/(16*(Real.log N)^(A/2+2))) := by field_simp;ring
  linarith

end PrimeSquares
