import PrimeSquares.GoldbachWeightedKernelUniform
import PrimeSquares.GoldbachWeightedKernelIntegration
import PrimeSquares.GoldbachLowerSmoothedSize

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

theorem goldbach_choose_positive_tolerance (F : ℝ→ℝ) (b : ℝ)
    (hF : ContinuousAt F 0) (hb : F 0<b) :
    ∃ ε : ℝ,0<ε ∧ ε<1/2 ∧ F ε<b := by
  have hInv : Tendsto (fun x : ℝ=>1/x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hh := (hF.tendsto.comp hInv).eventually (gt_mem_nhds hb)
  obtain ⟨x,hx,hFx⟩ := (eventually_ge_atTop (3:ℝ)).and hh |>.exists
  refine ⟨1/x,by positivity,?_,hFx⟩
  exact (div_lt_iff₀ (by linarith : 0<x)).mpr (by linarith)

theorem goldbach_weighted_moving_kernel_loss (N : ℕ) (z R m η : ℝ) (n : ℤ)
    (hN : 2≤N) (hz : 2≤z) (hm : 0<m) (hη : 0≤η) (hη1 : η<1)
    (hloss : Real.log ((N:ℝ)^2/m)≤η*Real.log z) :
    goldbachWeightedKernelSum (goldbachWeightedPairs N z) (fun i=>2*i.1*i.2)
      (fun i=>goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ)) m≤
      (1/(1-η)^2)*goldbachWeightedFixedKernel N z R n := by
  classical
  let I := goldbachWeightedPairs N z
  let F := fun i : ℕ×ℕ=>goldbachWeightedMultiplicative R n i.1/
    (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2)
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlogz : 0<Real.log z := Real.log_pos (by linarith)
  have hpoint : ∀ i∈I.filter (fun i=>2*((2*i.1*i.2:ℕ):ℝ)≤m),
      (goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))/
        (Real.log (m/((2*i.1*i.2:ℕ):ℝ)))^2≤(1/(1-η)^2)*F i := by
    intro i hi
    have hiI := (mem_filter.mp hi).1
    have hv := (mem_goldbach_weighted_pairs N z i).mp hiI
    have hℓ : (0:ℝ)<((2*i.1*i.2:ℕ):ℝ) := by
      have hh : 0<2*i.1*i.2 := mul_pos (mul_pos (by norm_num) hv.1) hv.2.2.1.pos
      exact_mod_cast hh
    have hh := (goldbach_weighted_log_loss ((N:ℝ)^2) m ((2*i.1*i.2:ℕ):ℝ) (Real.log z) η
      (sq_pos_of_pos hN0) hm hℓ hlogz hη hη1
      (goldbach_weighted_pair_log_floor N z hz i hiI) hloss).2
    have hw : 0≤goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ) :=
      div_nonneg (goldbach_weighted_multiplicative_nonneg R n _) hℓ.le
    have ht := mul_le_mul_of_nonneg_left hh hw
    convert ht using 1 <;> ring
  have hs := sum_le_sum hpoint
  rw [←mul_sum] at hs
  have hext : (∑ i∈I.filter (fun i=>2*((2*i.1*i.2:ℕ):ℝ)≤m),F i)≤∑ i∈I,F i :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _=>by
      dsimp only [F]
      exact div_nonneg (goldbach_weighted_multiplicative_nonneg R n _) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  exact hs.trans (mul_le_mul_of_nonneg_left hext (by positivity))

theorem goldbach_weighted_moving_kernel_uniform (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ K₂ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁)
    (hI : GoldbachClassicalIntervalMertens K₂) (C A η : ℝ)
    (hC : 0<C) (_hA : 0<A) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop,∀ n : ℤ,∀ m : ℝ,
      (N:ℝ)^2*(Real.log N)^(-A)≤m→m≤(N:ℝ)^2→
      goldbachWeightedKernelSum (goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ))) (fun i=>2*i.1*i.2)
        (fun i=>goldbachWeightedMultiplicative ((Real.log N)^C) n i.1/((2*i.1*i.2:ℕ):ℝ)) m≤
        (goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*
          (goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
          (Real.sqrt (Real.log ((Real.log N)^C))*Real.log N*Real.sqrt (Real.log N)) := by
  let B := goldbachHalfMeanConstant*goldbachWeightedW (9/8)
  let F := fun ε : ℝ=>(B+ε)/(1-ε)^2
  have hF : ContinuousAt F 0 := by
    have hd : (1-(0:ℝ))^2≠0 := by norm_num
    dsimp only [F]
    fun_prop
  obtain ⟨ε,hε,hεB,hFε⟩ := goldbach_choose_positive_tolerance F (B+η) hF (by
    dsimp only [F]
    norm_num
    linarith)
  have hRatio : Tendsto (fun L : ℝ=>A*Real.log L/L) atTop (nhds 0) := by
    simpa only [one_mul,add_zero,pow_one,mul_div_assoc,mul_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul A
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLog := Real.tendsto_log_atTop.comp hNat
  filter_upwards [goldbach_weighted_fixed_kernel_uniform hT K₀ K₁ K₂ hK₀ hK₁ hK₂ hM hV hI C ε hC hε,
    hLog.eventually (hRatio.eventually (gt_mem_nhds (mul_pos hε (by norm_num : (0:ℝ)<8/9)))),
    hNat.eventually (goldbach_retained_height_eventually A),hLog.eventually_ge_atTop 9,
    eventually_ge_atTop 2] with N hfixed hratio hheight hlog hN
  dsimp only [Function.comp_apply] at hratio hheight hlog
  intro n m hm hmN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog0 : 0<Real.log (N:ℝ) := by linarith
  have hm0 : 0<m := by linarith [hheight.1,hheight.2.trans hm]
  have hz : 2≤(N:ℝ)^(8/9:ℝ) := by
    rw [Real.rpow_def_of_pos hN0]
    have hh := Real.add_one_le_exp (Real.log (N:ℝ)*(8/9:ℝ))
    linarith
  have hquot : (N:ℝ)^2/m≤(Real.log N)^A := by
    rw [Real.rpow_neg hlog0.le,←div_eq_mul_inv] at hm
    apply (div_le_iff₀ hm0).mpr
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mp hm
    nlinarith only [hh]
  have hloss : Real.log ((N:ℝ)^2/m)≤ε*Real.log ((N:ℝ)^(8/9:ℝ)) := by
    have hh := Real.log_le_log (div_pos (sq_pos_of_pos hN0) hm0) hquot
    rw [Real.log_rpow hlog0] at hh
    rw [Real.log_rpow hN0]
    have hh' := (div_lt_iff₀ hlog0).mp hratio
    linarith
  have hmov := goldbach_weighted_moving_kernel_loss N ((N:ℝ)^(8/9:ℝ)) ((Real.log N)^C) m ε n
    hN hz hm0 hε.le (by linarith) hloss
  have hcoef : 0≤1/(1-ε)^2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left (hfixed n) hcoef
  have hratio0 : 0≤goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n := by
    have hR := (Real.rpow_pos_of_pos hlog0 C).le
    exact div_nonneg (goldbach_weighted_C_positive _ hR n).le (goldbach_weighted_B_positive _ hR n).le
  have hfac : 0≤(goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
      (Real.sqrt (Real.log ((Real.log N)^C))*Real.log N*Real.sqrt (Real.log N)) := by positivity
  have he : (1/(1-ε)^2)*((B+ε)*(goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
      (Real.sqrt (Real.log ((Real.log N)^C))*Real.log N*Real.sqrt (Real.log N)))=
      F ε*((goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
      (Real.sqrt (Real.log ((Real.log N)^C))*Real.log N*Real.sqrt (Real.log N))) := by
    dsimp only [F]
    ring
  dsimp only [B] at he
  rw [he] at hprod
  have hh := mul_le_mul_of_nonneg_right hFε.le hfac
  apply (hmov.trans (hprod.trans hh)).trans_eq
  dsimp only [B]
  ring

end PrimeSquares
