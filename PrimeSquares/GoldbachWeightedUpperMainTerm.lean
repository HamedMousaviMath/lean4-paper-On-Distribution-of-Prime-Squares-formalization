import PrimeSquares.GoldbachWeightedSourceBridge
import PrimeSquares.GoldbachWeightedSourceBudgets
import PrimeSquares.GoldbachWeightedLogComparisons

set_option autoImplicit false
open Filter
namespace PrimeSquares

/-- The source weighted upper main-term estimate, in uniform epsilon form.
The only independent analytic boundaries are the generic effective mean theorem
and the stated classical Mertens estimates. -/
theorem goldbach_weighted_upper_main_term_complete
    (hT : ClassicalHalfMeanValueInput) (K₀ K₁ K₂ : ℝ)
    (hK₀ : 0≤K₀) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁)
    (hI : GoldbachClassicalIntervalMertens K₂) (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (A : ℝ) (hA : 0<A) :
    ∀ C : ℝ,A+24≤C→∀ η : ℝ,0<η→∀ᶠ N : ℕ in atTop,∀ n : ℕ,
      (n:ZMod 24)=12→(N:ℝ)^2*(Real.log N)^(-A)≤n→n<N^2→
      goldbachWeightedUpperSum ψ N ((Real.log N)^C) n≤
        (goldbachWeightedUpperConstant (9/8)*goldbachWeightedW (9/8)+η)*
          (goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
            goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n) := by
  intro C hC η hη
  have hC0 : 0<C := by linarith
  obtain ⟨K,hK,hbridge⟩ := goldbach_weighted_source_bridge ψ hψ K₁ K₂ hK₁ hK₂ hV hI
  obtain ⟨Ks,hKs,hSmooth⟩ := goldbach_positive_singular_integral_complete ψ hψ
  let B := goldbachHalfMeanConstant*goldbachWeightedW (9/8)
  let F := fun ε : ℝ=>(48*(1+ε)*(B+ε)+ε)/(3*Real.sqrt (9/8:ℝ)*(1-ε)^2)
  let target := goldbachWeightedUpperConstant (9/8)*goldbachWeightedW (9/8)+η
  have hsα : 0<Real.sqrt (9/8:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hF : ContinuousAt F 0 := by
    have hd : 3*Real.sqrt (9/8:ℝ)*(1-(0:ℝ))^2≠0 := by positivity
    dsimp only [F]
    fun_prop
  have hF0 : F 0=goldbachWeightedUpperConstant (9/8)*goldbachWeightedW (9/8) := by
    dsimp only [F,B]
    norm_num only [add_zero,zero_add,sub_zero,one_pow,mul_one,one_mul]
    apply (div_eq_iff (show 3*Real.sqrt (9/8:ℝ)≠0 by positivity)).mpr
    have hh := congrArg (fun x : ℝ=>x*goldbachWeightedW (9/8))
      (goldbach_weighted_upper_constant_normalization (9/8) (by norm_num))
    nlinarith only [hh]
  obtain ⟨ε,hε,hεB,hFε⟩ := goldbach_choose_positive_tolerance F target hF (by
    rw [hF0]
    dsimp only [target]
    linarith)
  have hB : 0≤B := mul_nonneg goldbach_half_mean_constant_positive.le goldbach_weighted_W_nonneg
  have htarget : 0<target := by
    have hc := goldbach_weighted_upper_constant_positive (9/8) (by norm_num : (0:ℝ)<9/8)
    dsimp only [target]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le goldbach_weighted_W_nonneg) hη
  filter_upwards [goldbach_weighted_source_budgets A C K₁ Ks K (goldbachWeightedMassConstant K₂) ε hC0 hε,
    goldbach_weighted_moving_kernel_uniform hT K₀ K₁ K₂ hK₀ hK₁ hK₂ hM hV hI
      C (A+14) ε hC0 (by linarith) hε] with N hbud hKernel
  obtain ⟨hN,hL,hR,hRN,hqL,hKq,hKsL,hErr,hN64,hRet,hRetT⟩ := hbud
  intro n hn24 hret hnN
  have hN0 : (0:ℝ)<N := by linarith
  have hL0 : 0<Real.log (N:ℝ) := by linarith
  have hR0 : 0<(Real.log N)^C := by linarith
  have hn64 : 64≤n := by exact_mod_cast hN64.trans (hRet.trans hret)
  have hn24' : ((n:ℤ):ZMod 24)=12 := by simpa only [Int.cast_natCast] using hn24
  have hT : 2≤(N:ℝ)^2*(Real.log N)^(-(A+14)) := by linarith
  have hbridge' := hbridge A C ε hA hC hε N n hN hL hn64 hnN hn24' hret hR hRN hqL
    (by linarith) hT (hKernel n)
  obtain ⟨hSpos,hU⟩ := hbridge'
  have hcoef : 48*(1+K₁/Real.log ((Real.log N)^C))*(B+ε)+
      ((768*goldbachWeightedMassConstant K₂/(Real.log 2)^3)/(Real.log N)^3+
        (48*goldbachWeightedMassConstant K₂*K)/(Real.log N)^2)≤48*(1+ε)*(B+ε)+ε := by
    have hh := mul_le_mul_of_nonneg_right (show 1+K₁/Real.log ((Real.log N)^C)≤1+ε by linarith)
      (show 0≤48*(B+ε) by positivity)
    nlinarith only [hh,hErr]
  have hU' : goldbachWeightedUpperSum ψ N ((Real.log N)^C) n≤
      (48*(1+ε)*(B+ε)+ε)*goldbachWeightedReference N ((Real.log N)^C) n :=
    hU.trans (mul_le_mul_of_nonneg_right hcoef hSpos.le)
  have hH := goldbach_archimedean_retained_lower A N n hN hn64 hnN.le hret
  have hH0 := goldbach_weighted_arch_real_nonneg N n 1
  have hs := (hSmooth N 1 (by omega) (by decide) ((Real.log N)^C) N ((N:ℝ)^2) n
    hR0 (by exact_mod_cast hN) le_rfl (by nlinarith) (by exact_mod_cast hnN)).2.2
  have he := goldbach_weighted_smoothing_relative A C Ks N (Real.log N)
    (goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re
    (by linarith) (by linarith) hKs.le hN0.le hH
  have he' := he.trans (mul_le_mul_of_nonneg_right hKsL hH0)
  have hRe := (Complex.abs_re_le_norm
    (goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)-
      goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2))).trans hs
  have hneg := neg_abs_le
    (goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)-
      goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re
  simp only [Complex.sub_re] at hRe hneg
  have hHsm : (1-ε)*(goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re≤
      (goldbachSingularIntegral ψ N 1 ((Real.log N)^C) n (N:ℝ) ((N:ℝ)^2)).re := by
    nlinarith only [hRe,hneg,he']
  have hRz : (Real.log N)^C<(N:ℝ)^(8/9:ℝ) := hRN.trans_le
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (by norm_num : (2/9:ℝ)≤8/9))
  have hLower := goldbach_weighted_lower_outer ψ N n ((Real.log N)^C) K₁ ε hN hR hRz
    hK₁ hV hε.le (by linarith) hKq hn24' hHsm
  have hden : 0<3*Real.sqrt (9/8:ℝ)*(1-ε)^2 := by
    have hh : 0<1-ε := by linarith
    positivity
  have hconst : 48*(1+ε)*(B+ε)+ε≤target*(3*Real.sqrt (9/8:ℝ)*(1-ε)^2) :=
    ((div_lt_iff₀ hden).mp hFε).le
  have hCompare := mul_le_mul_of_nonneg_right hconst hSpos.le
  have hScaled := mul_le_mul_of_nonneg_left hLower htarget.le
  apply (hU'.trans hCompare).trans
  convert hScaled using 1;dsimp only [target];ring

end PrimeSquares
