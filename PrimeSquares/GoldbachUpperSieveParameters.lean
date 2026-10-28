import PrimeSquares.GoldbachLowerSieveParameters
import PrimeSquares.GoldbachWeightedGeometry

set_option autoImplicit false
open Filter
namespace PrimeSquares

noncomputable def goldbachUpperSieveLimit (N : ℝ) (ℓ : ℕ) : ℝ :=
  (N^2/(ℓ:ℝ))^(1/4:ℝ)

noncomputable def goldbachUpperDivisorLevel (B N : ℝ) (ℓ : ℕ) : ℝ :=
  Real.sqrt (N^2/(ℓ:ℝ))/(12*(Real.log N)^B)

noncomputable def goldbachUpperOuterLevel (B N : ℝ) (ℓ : ℕ) : ℝ :=
  goldbachUpperDivisorLevel B N ℓ/Real.exp ((Real.log (Real.log N))^3)

noncomputable def goldbachUpperLogLoss (B N : ℝ) : ℝ :=
  Real.log 12+B*Real.log (Real.log N)+(Real.log (Real.log N))^3

theorem goldbach_upper_log_loss_ratio (B : ℝ) :
    Tendsto (fun N : ℝ=>goldbachUpperLogLoss B N/Real.log N) atTop (nhds 0) := by
  have h₁ : Tendsto (fun N : ℝ=>Real.log (Real.log N)/Real.log N) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Real.tendsto_log_atTop
  have h₃ : Tendsto (fun N : ℝ=>(Real.log (Real.log N))^3/Real.log N) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp Real.tendsto_log_atTop
  have hc : Tendsto (fun N : ℝ=>Real.log 12/Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  simpa only [goldbachUpperLogLoss,add_div,mul_div_assoc,add_zero,zero_add,mul_zero] using (hc.add (h₁.const_mul B)).add h₃

theorem goldbach_upper_sieve_log_geometry (N : ℝ) (ℓ : ℕ) (hN : 1<N)
    (hℓ : 1≤ℓ) (hℓB : (ℓ:ℝ)≤N^(10/9:ℝ)) :
    0<goldbachUpperSieveLimit N ℓ ∧
      (2/9:ℝ)*Real.log N≤Real.log (goldbachUpperSieveLimit N ℓ) ∧
      Real.log (goldbachUpperSieveLimit N ℓ)≤(1/2:ℝ)*Real.log N := by
  have hN0 : 0<N := by linarith
  have hℓ0 : (0:ℝ)<ℓ := by exact_mod_cast (show 0<ℓ by omega)
  have hlogℓ0 : 0≤Real.log (ℓ:ℝ) := Real.log_nonneg (by exact_mod_cast hℓ)
  have hlogℓ := Real.log_le_log hℓ0 hℓB
  rw [Real.log_rpow hN0] at hlogℓ
  have hpos : 0<goldbachUpperSieveLimit N ℓ := Real.rpow_pos_of_pos (div_pos (sq_pos_of_pos hN0) hℓ0) _
  have he : Real.log (goldbachUpperSieveLimit N ℓ)=(1/4:ℝ)*(2*Real.log N-Real.log (ℓ:ℝ)) := by
    rw [goldbachUpperSieveLimit,Real.log_rpow (div_pos (sq_pos_of_pos hN0) hℓ0),
      Real.log_div (sq_pos_of_pos hN0).ne' hℓ0.ne',Real.log_pow]
    norm_num
  exact ⟨hpos,by rw [he];linarith,by rw [he];linarith⟩

theorem goldbach_upper_outer_log (B N : ℝ) (ℓ : ℕ) (hN : 1<N) (hℓ : 0<ℓ) :
    0<goldbachUpperOuterLevel B N ℓ ∧
      Real.log (goldbachUpperOuterLevel B N ℓ)=
        2*Real.log (goldbachUpperSieveLimit N ℓ)-goldbachUpperLogLoss B N := by
  have hN0 : 0<N := by linarith
  have hℓ0 : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hq : 0<N^2/(ℓ:ℝ) := div_pos (sq_pos_of_pos hN0) hℓ0
  have hL := Real.log_pos hN
  have hp := Real.rpow_pos_of_pos hL B
  constructor
  · exact div_pos (div_pos (Real.sqrt_pos.mpr hq) (mul_pos (by norm_num) hp)) (Real.exp_pos _)
  · rw [goldbachUpperOuterLevel,goldbachUpperDivisorLevel,
      Real.log_div (div_pos (Real.sqrt_pos.mpr hq) (mul_pos (by norm_num) hp)).ne' (Real.exp_ne_zero _),
      Real.log_div (Real.sqrt_pos.mpr hq).ne' (mul_ne_zero (by norm_num) hp.ne'),
      Real.log_mul (by norm_num) hp.ne',Real.log_rpow hL,Real.log_exp,Real.log_sqrt hq.le,
      goldbachUpperSieveLimit,Real.log_rpow hq,goldbachUpperLogLoss]
    ring

theorem goldbach_upper_sieve_levels_uniform (B C : ℝ) (hB : 0≤B) :
    ∀ᶠ N : ℝ in atTop,1<N ∧ ∀ ℓ : ℕ,1≤ℓ→(ℓ:ℝ)≤N^(10/9:ℝ)→
      (Real.log N)^C+1≤goldbachUpperSieveLimit N ℓ ∧
      goldbachUpperSieveLimit N ℓ≤goldbachUpperOuterLevel B N ℓ ∧
      goldbachUpperOuterLevel B N ℓ≤N^(2:ℝ) := by
  have he := (goldbach_upper_log_loss_ratio B).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<2/9))
  filter_upwards [eventually_gt_atTop (Real.exp 1),he,
    eventually_two_rpow_budget (K:=1) (L:=1) (a:=(1:ℝ)/9) (d:=0) (b:=(2:ℝ)/9)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_log_rpow_le_rpow C (by norm_num : (0:ℝ)<1/9)] with N hN he hp hlog
  have hN1 : 1<N := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans hN
  have hN0 : 0<N := by linarith
  have hL : 0<Real.log N := Real.log_pos hN1
  have ht : 0≤Real.log (Real.log N) := Real.log_nonneg (by
    have hh := Real.log_lt_log (Real.exp_pos 1) hN
    rw [Real.log_exp] at hh;linarith)
  have hE : 0≤goldbachUpperLogLoss B N := by
    unfold goldbachUpperLogLoss
    exact add_nonneg (add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg hB ht)) (pow_nonneg ht _)
  refine ⟨hN1,?_⟩
  intro ℓ hℓ hℓB
  obtain ⟨hz,hzl,hzu⟩ := goldbach_upper_sieve_log_geometry N ℓ hN1 hℓ hℓB
  obtain ⟨hD,hDe⟩ := goldbach_upper_outer_log B N ℓ hN1 (by omega)
  have hElow : goldbachUpperLogLoss B N≤(2/9:ℝ)*Real.log N :=
    ((div_lt_iff₀ hL).mp he).le
  refine ⟨?_,?_,?_⟩
  · have hpow : N^(2/9:ℝ)≤goldbachUpperSieveLimit N ℓ := by
      apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hN0 _) hz).mp
      rwa [Real.log_rpow hN0]
    have hsum : N^(1/9:ℝ)+1≤N^(2/9:ℝ) := by
      simpa only [one_mul,Real.rpow_zero] using hp
    have hh : (Real.log N)^C+1≤N^(2/9:ℝ) := by linarith only [hlog,hsum]
    exact hh.trans hpow
  · apply (Real.log_le_log_iff hz hD).mp
    rw [hDe]
    linarith
  · apply (Real.log_le_log_iff hD (Real.rpow_pos_of_pos hN0 _)).mp
    rw [hDe,Real.log_rpow hN0]
    linarith

theorem goldbach_upper_parameter_along (B : ℝ) (ℓ : ℝ→ℕ)
    (hℓ : ∀ᶠ N : ℝ in atTop,1<N ∧ 1≤ℓ N ∧ (ℓ N:ℝ)≤N^(10/9:ℝ)) :
    Tendsto (fun N : ℝ=>Real.log (goldbachUpperOuterLevel B N (ℓ N))/
      Real.log (goldbachUpperSieveLimit N (ℓ N))) atTop (nhds 2) := by
  have herr : Tendsto (fun N : ℝ=>goldbachUpperLogLoss B N/
      Real.log (goldbachUpperSieveLimit N (ℓ N))) atTop (nhds 0) := by
    have hh : Tendsto (fun N : ℝ=>(9/2:ℝ)*‖goldbachUpperLogLoss B N/Real.log N‖) atTop (nhds 0) := by
      simpa using (goldbach_upper_log_loss_ratio B).norm.const_mul (9/2:ℝ)
    apply squeeze_zero_norm' _ hh
    filter_upwards [hℓ] with N hN
    obtain ⟨hN,hℓ,hℓB⟩ := hN
    obtain ⟨_,hzl,_⟩ := goldbach_upper_sieve_log_geometry N (ℓ N) hN hℓ hℓB
    have hL := Real.log_pos hN
    have hZ : 0<Real.log (goldbachUpperSieveLimit N (ℓ N)) := (by positivity : 0<(2/9:ℝ)*Real.log N).trans_le hzl
    simp only [Real.norm_eq_abs,abs_div,abs_of_pos hL,abs_of_pos hZ]
    calc
      _≤|goldbachUpperLogLoss B N|/((2/9:ℝ)*Real.log N) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hzl
      _=_ := by field_simp
  have hconst : Tendsto (fun _ : ℝ=>(2:ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have hh : Tendsto (fun N : ℝ=>2-goldbachUpperLogLoss B N/Real.log (goldbachUpperSieveLimit N (ℓ N))) atTop (nhds 2) := by
    simpa using hconst.sub herr
  apply hh.congr'
  filter_upwards [hℓ] with N hN
  obtain ⟨hN,hℓ,hℓB⟩ := hN
  have he := (goldbach_upper_outer_log B N (ℓ N) hN (by omega)).2
  obtain ⟨_,hzl,_⟩ := goldbach_upper_sieve_log_geometry N (ℓ N) hN hℓ hℓB
  have hz : Real.log (goldbachUpperSieveLimit N (ℓ N))≠0 := by
    have := Real.log_pos hN
    have hh : 0<(2/9:ℝ)*Real.log N := by positivity
    exact (hh.trans_le hzl).ne'
  rw [he]
  field_simp

theorem goldbach_upper_product_level (B N : ℝ) (ℓ : ℕ) :
    Real.exp ((Real.log (Real.log N))^3)*goldbachUpperOuterLevel B N ℓ=
      goldbachUpperDivisorLevel B N ℓ := by
  unfold goldbachUpperOuterLevel
  exact mul_div_cancel₀ _ (Real.exp_ne_zero _)

end PrimeSquares
