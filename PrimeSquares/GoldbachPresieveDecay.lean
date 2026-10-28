import PrimeSquares.GoldbachPresieveCoefficientAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_presieve_gaussian_decay (a b B : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ=>t^B*Real.exp (-a*t^2+b*t)) atTop (nhds 0) := by
  have hlo : ∀ᶠ t : ℝ in atTop,0≤t^B*Real.exp (-a*t^2+b*t) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht B) (Real.exp_pos _).le
  have hhi : ∀ᶠ t : ℝ in atTop,t^B*Real.exp (-a*t^2+b*t)≤t^B*Real.exp (-t) := by
    filter_upwards [eventually_ge_atTop (0:ℝ),eventually_ge_atTop ((b+1)/a)] with t ht ht'
    have hprod : b+1≤a*t := by simpa only [mul_comm t a] using (div_le_iff₀ ha).mp ht'
    have hpoly : -a*t^2+b*t≤ -t := by nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpoly) (Real.rpow_nonneg ht B)
  have hlim : Tendsto (fun t : ℝ=>t^B*Real.exp (-t)) atTop (nhds 0) := by
    simpa only [neg_one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero B 1 zero_lt_one
  exact squeeze_zero' hlo hhi hlim

theorem goldbach_presieve_polylog_decay (a b B : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℝ=>(Real.log (Real.log N))^B*
      Real.exp (-a*(Real.log (Real.log N))^2)*(Real.log N)^b) atTop (nhds 0) := by
  have h := (goldbach_presieve_gaussian_decay a b B ha).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
  dsimp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (Real.log_pos hN)]
  rw [Real.exp_add]
  rw [mul_comm b (Real.log (Real.log N))]
  ring

theorem goldbach_presieve_preliminary_ratio (C t : ℝ) (hC : 0 < C) (ht : 1≤t) :
    t^2/(C+1)≤Real.log (Real.exp (t^3))/Real.log (Real.exp (C*t)+1) := by
  rw [Real.log_exp]
  have ht0 : 0≤t := by linarith
  have he : 1≤Real.exp (C*t) := Real.one_le_exp_iff.mpr (mul_nonneg hC.le ht0)
  have hlog : 0 < Real.log (Real.exp (C*t)+1) := Real.log_pos (by linarith)
  have hbound : Real.log (Real.exp (C*t)+1)≤(C+1)*t := by
    calc
      _≤Real.log (2*Real.exp (C*t)) :=
        Real.log_le_log (by linarith) (by linarith)
      _=Real.log 2+C*t := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
      _≤_ := by have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2);nlinarith
  apply (div_le_div_iff₀ (by linarith : 0 < C+1) hlog).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (sq_nonneg t)]

theorem goldbach_presieve_preliminary_error_bound (C c K t : ℝ)
    (hC : 0 < C) (hc : 0≤c) (hK : 0≤K) (ht : 1≤t) :
    K*Real.exp (-c*(Real.log (Real.exp (t^3))/Real.log (Real.exp (C*t)+1)))≤
      K*Real.exp (-(c/(C+1))*t^2) := by
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonpos_left (goldbach_presieve_preliminary_ratio C t hC ht) (neg_nonpos.mpr hc)
  convert h using 1
  ring

noncomputable def goldbachPresievePreliminaryS (C N : ℝ) : ℝ :=
  (Real.log (Real.log N))^3/Real.log (Real.exp (C*Real.log (Real.log N))+1)

theorem goldbach_presieve_preliminary_s_tendsto (C : ℝ) (hC : 0 < C) :
    Tendsto (goldbachPresievePreliminaryS C) atTop atTop := by
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  rw [tendsto_atTop]
  intro B
  filter_upwards [ht.eventually_ge_atTop (max 1 (B*(C+1)))] with N hN
  have h1 : 1≤Real.log (Real.log N) := (le_max_left _ _).trans hN
  have hB : B*(C+1)≤Real.log (Real.log N) := (le_max_right _ _).trans hN
  have hquad : B≤(Real.log (Real.log N))^2/(C+1) := by
    apply (le_div_iff₀ (by linarith : 0 < C+1)).mpr
    nlinarith
  apply hquad.trans
  simpa only [goldbachPresievePreliminaryS,Real.log_exp] using
    goldbach_presieve_preliminary_ratio C (Real.log (Real.log N)) hC h1

theorem goldbach_presieve_preliminary_level_eventually (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℝ in atTop,
      Real.exp (C*Real.log (Real.log N))+1≤Real.exp ((Real.log (Real.log N))^3) := by
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [(goldbach_presieve_preliminary_s_tendsto C hC).eventually_ge_atTop 1,
    ht.eventually_ge_atTop 1] with N hS htN
  have he : 1 < Real.exp (C*Real.log (Real.log N)) :=
    Real.one_lt_exp_iff.mpr (mul_pos hC (by change 1≤Real.log (Real.log N) at htN;linarith))
  have hR : 0 < Real.exp (C*Real.log (Real.log N))+1 := by linarith
  have hlog : 0 < Real.log (Real.exp (C*Real.log (Real.log N))+1) := Real.log_pos (by linarith)
  have hh : Real.log (Real.exp (C*Real.log (Real.log N))+1)≤(Real.log (Real.log N))^3 := by
    have h := (le_div_iff₀ hlog).mp hS
    simpa only [one_mul] using h
  have h := Real.exp_le_exp.mpr hh
  simpa only [Real.exp_log hR] using h

theorem goldbach_presieve_preliminary_absorption (C c K b : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hK : 0≤K) :
    Tendsto (fun N : ℝ=>K*Real.exp (-c*goldbachPresievePreliminaryS C N)*(Real.log N)^b)
      atTop (nhds 0) := by
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ha : 0 < c/(C+1) := div_pos hc (by linarith)
  have hlim := (goldbach_presieve_polylog_decay (c/(C+1)) b 0 ha).const_mul K
  simp only [Real.rpow_zero,one_mul,mul_zero] at hlim
  have hlo : ∀ᶠ N : ℝ in atTop,0≤K*Real.exp (-c*goldbachPresievePreliminaryS C N)*(Real.log N)^b := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
    exact mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (Real.rpow_nonneg (Real.log_pos hN).le b)
  have hhi : ∀ᶠ N : ℝ in atTop,
      K*Real.exp (-c*goldbachPresievePreliminaryS C N)*(Real.log N)^b≤
      K*(Real.exp (-(c/(C+1))*(Real.log (Real.log N))^2)*(Real.log N)^b) := by
    filter_upwards [ht.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with N hN hN'
    have h := goldbach_presieve_preliminary_error_bound C c K (Real.log (Real.log N)) hC hc.le hK hN
    simp only [Real.log_exp] at h
    simpa only [goldbachPresievePreliminaryS,mul_assoc] using
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (Real.log_pos hN').le b)
  exact squeeze_zero' hlo hhi hlim

theorem goldbach_presieve_outer_level_tendsto (C : ℝ) (hC : 0 < C) (D : ℝ→ℝ)
    (hD : ∀ᶠ N : ℝ in atTop,Real.exp (C*Real.log (Real.log N))+1≤D N) :
    Tendsto D atTop atTop := by
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  rw [tendsto_atTop]
  intro B
  filter_upwards [hD,ht.eventually_ge_atTop (Real.log (max 1 B)/C)] with N hN htN
  have hCt : Real.log (max 1 B)≤C*Real.log (Real.log N) := by
    simpa only [Function.comp_apply,mul_comm _ C] using (div_le_iff₀ hC).mp htN
  have hB : B≤Real.exp (C*Real.log (Real.log N))+1 := by
    calc
      B≤max 1 B := le_max_right _ _
      _=Real.exp (Real.log (max 1 B)) := (Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).symm
      _≤Real.exp (C*Real.log (Real.log N)) := Real.exp_le_exp.mpr hCt
      _≤_ := by linarith
  exact hB.trans hN

theorem goldbach_presieve_outer_error_tendsto (D : ℝ→ℝ)
    (hD : Tendsto D atTop atTop) (K δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℝ=>K*(Real.log (D N))^(-δ)) atTop (nhds 0) := by
  simpa only [Function.comp_apply,mul_zero] using
    ((tendsto_rpow_neg_atTop hδ).comp (Real.tendsto_log_atTop.comp hD)).const_mul K

theorem goldbach_presieve_total_error_tendsto (C c K₀ K₁ δ b : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hK₀ : 0≤K₀) (hδ : 0 < δ) (D : ℝ→ℝ)
    (hD : ∀ᶠ N : ℝ in atTop,Real.exp (C*Real.log (Real.log N))+1≤D N) :
    Tendsto (fun N : ℝ=>K₁*(Real.log (D N))^(-δ)+
      K₀*Real.exp (-c*goldbachPresievePreliminaryS C N)*(Real.log N)^b)
      atTop (nhds 0) := by
  have ho := goldbach_presieve_outer_error_tendsto D
    (goldbach_presieve_outer_level_tendsto C hC D hD) K₁ δ hδ
  have hp := goldbach_presieve_preliminary_absorption C c K₀ b hC hc hK₀
  simpa only [zero_add] using ho.add hp

theorem goldbach_presieve_uniform_error_tendsto (C c K₀ K₁ K₂ δ κ : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hK₀ : 0≤K₀) (hδ : 0 < δ) (D : ℝ→ℝ)
    (hD : ∀ᶠ N : ℝ in atTop,Real.exp (C*Real.log (Real.log N))+1≤D N) :
    Tendsto (fun N : ℝ=>K₁*(Real.log (D N))^(-δ)+
      (K₀*Real.exp (-c*goldbachPresievePreliminaryS C N))*(K₂*(Real.log N)^κ)^2)
      atTop (nhds 0) := by
  have h := goldbach_presieve_total_error_tendsto C c (K₀*K₂^2) K₁ δ (2*κ)
    hC hc (mul_nonneg hK₀ (sq_nonneg K₂)) hδ D hD
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
  have hp : ((Real.log N)^κ)^2=(Real.log N)^(2*κ) := by
    rw [show (2:ℝ)*κ=κ*(2:ℝ) by ring,Real.rpow_mul (Real.log_pos hN).le κ 2,Real.rpow_two]
  rw [mul_pow,hp]
  ring

end PrimeSquares
