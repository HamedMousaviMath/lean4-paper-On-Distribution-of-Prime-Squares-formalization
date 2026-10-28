import PrimeSquares.GoldbachWeightedArchimedean
import PrimeSquares.GoldbachArchimedeanLower
import PrimeSquares.GoldbachWeightedFiniteIntegration

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachWeightedKernelSum {ι : Type*} (I : Finset ι)
    (ℓ : ι→ℕ) (w : ι→ℝ) (m : ℝ) : ℝ := by
  classical
  exact ∑ i∈I.filter (fun i=>2*(ℓ i:ℝ)≤m),w i/(Real.log (m/(ℓ i:ℝ)))^2

theorem goldbach_weighted_arch_pointwise (N m u w : ℝ) (ℓ : ℕ)
    (hℓ : 0<ℓ) (hu : 2≤u) (hw : 0≤w) (hm : m≤N^2) (hbase : 2≤N^2/(ℓ:ℝ)) :
    w/Real.log (N^2/(ℓ:ℝ))*((Real.log u)⁻¹*(goldbachLogWindow (N^2) (m/(ℓ:ℝ))).re)≤
      (Real.log u)⁻¹*(if 2*(ℓ:ℝ)≤m then w/(Real.log (m/(ℓ:ℝ)))^2 else 0) := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hlogu : 0<Real.log u := Real.log_pos (by linarith)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hLB : 0<Real.log (N^2/(ℓ:ℝ)) := Real.log_pos (by linarith)
  by_cases hwin : m/(ℓ:ℝ)∈Set.Icc (2:ℝ) (N^2)
  · have hcut : 2*(ℓ:ℝ)≤m := (le_div_iff₀ hl).mp hwin.1
    rw [ite_eq_left hcut,goldbachLogWindow,Set.indicator_of_mem hwin,Complex.ofReal_re]
    have hLm : 0<Real.log (m/(ℓ:ℝ)) := Real.log_pos (by linarith [hwin.1])
    have hL : Real.log (m/(ℓ:ℝ))≤Real.log (N^2/(ℓ:ℝ)) :=
      Real.log_le_log (by linarith [hwin.1]) (div_le_div_of_nonneg_right hm hl.le)
    have hprod : (Real.log (m/(ℓ:ℝ)))^2≤
        Real.log (N^2/(ℓ:ℝ))*Real.log (m/(ℓ:ℝ)) := by
      nlinarith only [mul_le_mul_of_nonneg_right hL hLm.le]
    have hh := mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (sq_pos_of_pos hLm) hprod)
      (mul_nonneg hw (inv_nonneg.mpr hlogu.le))
    convert hh using 1 <;> field_simp
  · rw [goldbachLogWindow,Set.indicator_of_notMem hwin,Complex.zero_re,mul_zero,mul_zero]
    split_ifs <;> positivity

theorem goldbach_weighted_arch_sum_pointwise {ι : Type*} (I : Finset ι)
    (N n u : ℝ) (ℓ : ι→ℕ) (w : ι→ℝ)
    (hℓ : ∀ i∈I,0<ℓ i) (hu : 2≤u) (hw : ∀ i∈I,0≤w i)
    (hn : n≤N^2) (hbase : ∀ i∈I,2≤N^2/(ℓ i:ℝ)) :
    (∑ i∈I,w i/Real.log (N^2/(ℓ i:ℝ))*goldbachWeightedArchIntegrand N (ℓ i) (n-1) u)≤
      (Real.log u)⁻¹*goldbachWeightedKernelSum I ℓ w (n-1-u^2) := by
  classical
  unfold goldbachWeightedKernelSum
  rw [sum_filter,mul_sum]
  apply sum_le_sum
  intro i hi
  exact goldbach_weighted_arch_pointwise N (n-1-u^2) u (w i) (ℓ i) (hℓ i hi) hu
    (hw i hi) (by nlinarith [sq_nonneg u]) (hbase i hi)

theorem goldbach_weighted_arch_retained_pointwise {ι : Type*} (I : Finset ι)
    (N n u T B : ℝ) (ℓ : ι→ℕ) (w : ι→ℝ)
    (_hN : 2≤N) (hℓ : ∀ i∈I,0<ℓ i) (hu : u∈Set.Icc 2 N)
    (hw : ∀ i∈I,0≤w i) (hn : n≤N^2) (hbase : ∀ i∈I,2≤N^2/(ℓ i:ℝ))
    (hT : 2≤T) (hret : T≤n-1-u^2) (hB : 0≤B)
    (hkernel : goldbachWeightedKernelSum I ℓ w (n-1-u^2)≤B) :
    (∑ i∈I,w i/Real.log (N^2/(ℓ i:ℝ))*goldbachWeightedArchIntegrand N (ℓ i) (n-1) u)≤
      2*B*Real.log N*goldbachLowerArchIntegrand N n u := by
  have hp := goldbach_weighted_arch_sum_pointwise I N n u ℓ w hℓ hu.1 hw hn hbase
  have hlogu : 0<Real.log u := Real.log_pos (by linarith [hu.1])
  have hv : n-u^2∈Set.Icc (2:ℝ) (N^2) := ⟨by linarith,by nlinarith [sq_nonneg u]⟩
  have hlogv : 0<Real.log (n-u^2) := Real.log_pos (by linarith [hv.1])
  have hlogvN : Real.log (n-u^2)≤2*Real.log N := by
    have hh := Real.log_le_log (by linarith [hv.1]) hv.2
    rwa [Real.log_pow] at hh
  apply (hp.trans (mul_le_mul_of_nonneg_left hkernel (inv_nonneg.mpr hlogu.le))).trans
  unfold goldbachLowerArchIntegrand
  rw [goldbachLogWindow,Set.indicator_of_mem hv,Complex.ofReal_re]
  have hh := mul_le_mul_of_nonneg_left hlogvN
    (div_nonneg hB (mul_pos hlogu hlogv).le)
  convert hh using 1 <;> field_simp

theorem goldbach_weighted_arch_coarse (N n u w : ℝ) (ℓ : ℕ) (hu : 2≤u)
    (hw : 0≤w) (hbase : 2≤N^2/(ℓ:ℝ)) :
    w/Real.log (N^2/(ℓ:ℝ))*goldbachWeightedArchIntegrand N ℓ n u≤w/(Real.log 2)^3 := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlogu : Real.log 2≤Real.log u := Real.log_le_log (by norm_num) hu
  have hlogu0 : 0<Real.log u := hlog2.trans_le hlogu
  have hlogB : Real.log 2≤Real.log (N^2/(ℓ:ℝ)) := Real.log_le_log (by norm_num) hbase
  have hV : 0≤(goldbachLogWindow (N^2) ((n-u^2)/(ℓ:ℝ))).re := by
    unfold goldbachLogWindow
    by_cases h : (n-u^2)/(ℓ:ℝ)∈Set.Icc (2:ℝ) (N^2)
    · rw [Set.indicator_of_mem h,Complex.ofReal_re]
      exact inv_nonneg.mpr (Real.log_nonneg (by linarith [h.1]))
    · simp only [Set.indicator_of_notMem h,Complex.zero_re,le_refl]
  have hVB : (goldbachLogWindow (N^2) ((n-u^2)/(ℓ:ℝ))).re≤1/Real.log 2 :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (goldbach_log_window_norm _ _))
  have hwB := div_le_div_of_nonneg_left hw hlog2 hlogB
  have huB := one_div_le_one_div_of_le hlog2 hlogu
  have hmain := mul_le_mul
    (mul_le_mul hwB huB (one_div_nonneg.mpr hlogu0.le)
      (div_nonneg hw hlog2.le)) hVB hV
      (mul_nonneg (div_nonneg hw hlog2.le) (by positivity : (0:ℝ)≤1/Real.log 2))
  dsimp only [goldbachWeightedArchIntegrand]
  convert hmain using 1 <;> simp only [div_eq_mul_inv,pow_succ] <;> ring

theorem goldbach_weighted_arch_kernel_integrated {ι : Type*} (I : Finset ι)
    (N : ℕ) (n T B : ℝ) (ℓ : ι→ℕ) (w : ι→ℝ)
    (hN : 2≤N) (hn : 4≤n) (hnN : n≤(N:ℝ)^2) (hT : 2≤T) (hTn : T≤n/4)
    (hB : 0≤B) (hℓ : ∀ i∈I,0<ℓ i) (hw : ∀ i∈I,0≤w i)
    (hbase : ∀ i∈I,2≤(N:ℝ)^2/(ℓ i:ℝ))
    (hkernel : ∀ m : ℝ,T≤m→m≤(N:ℝ)^2→goldbachWeightedKernelSum I ℓ w m≤B) :
    (∑ i∈I,w i/Real.log ((N:ℝ)^2/(ℓ i:ℝ))*
      (goldbachArchimedeanIntegral (ℓ i) (n-1) (N:ℝ) ((N:ℝ)^2)).re)≤
        2*B*Real.log N*(goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re+
          (2*T/Real.sqrt n)*(∑ i∈I,w i)/(Real.log 2)^3 := by
  classical
  let F := fun u : ℝ=>∑ i∈I,w i/Real.log ((N:ℝ)^2/(ℓ i:ℝ))*
    goldbachWeightedArchIntegrand N (ℓ i) (n-1) u
  let K := (∑ i∈I,w i)/(Real.log 2)^3
  let S := {u : ℝ | 2≤u ∧ 0<n-1-u^2 ∧ n-1-u^2<T}
  let G := fun u : ℝ=>2*B*Real.log N*goldbachLowerArchIntegrand N n u
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hlogN : 0<Real.log N := Real.log_pos (by linarith)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0≤K := div_nonneg (sum_nonneg hw) (pow_nonneg hlog2.le _)
  have hSm : MeasurableSet S := by
    dsimp only [S]
    have hm : Measurable (fun u : ℝ=>n-1-u^2) := by fun_prop
    exact measurableSet_Ici.inter ((measurableSet_Ioi.preimage hm).inter (measurableSet_Iio.preimage hm))
  have hSfin : volume S≠⊤ := by
    apply (lt_of_le_of_lt (measure_mono
      (goldbach_weighted_thin_window_subset n T hn (by linarith) hTn))
      (lt_of_le_of_lt (measure_mono Set.Ioo_subset_Icc_self) isCompact_Icc.measure_lt_top)).ne
  have hFi : IntegrableOn F (Set.Icc (2:ℝ) (N:ℝ)) := by
    apply integrable_finsetSum
    intro i hi
    exact (goldbach_weighted_arch_integrand_integrable N (n-1) (ℓ i)).const_mul _
  have hGi : IntegrableOn G (Set.Icc (2:ℝ) (N:ℝ)) :=
    (goldbach_lower_arch_integrand_integrable N n).const_mul _
  have hKi : IntegrableOn (S.indicator (fun _ : ℝ=>K)) (Set.Icc (2:ℝ) (N:ℝ)) :=
    (integrableOn_const isCompact_Icc.measure_ne_top).indicator hSm
  have hpoint : ∀ u∈Set.Icc (2:ℝ) (N:ℝ),F u≤G u+S.indicator (fun _ : ℝ=>K) u := by
    intro u hu
    have hG : 0≤G u := mul_nonneg (by positivity)
      (goldbach_lower_arch_integrand_nonneg N n u hu.1)
    have hKind : 0≤S.indicator (fun _ : ℝ=>K) u := by
      by_cases h : u∈S
      · rw [Set.indicator_of_mem h];exact hK
      · rw [Set.indicator_of_notMem h]
    by_cases hret : T≤n-1-u^2
    · have hh := goldbach_weighted_arch_retained_pointwise I N n u T B ℓ w hNr hℓ hu hw hnN hbase hT hret hB
        (hkernel _ hret (by nlinarith [sq_nonneg u]))
      exact hh.trans (by dsimp only [G];linarith only [hKind])
    · have hsmall : n-1-u^2<T := lt_of_not_ge hret
      by_cases hm : 0<n-1-u^2
      · have huS : u∈S := ⟨hu.1,hm,hsmall⟩
        rw [Set.indicator_of_mem huS]
        have hcoarse : F u≤K := by
          dsimp only [F,K]
          rw [sum_div]
          exact sum_le_sum (fun i hi=>goldbach_weighted_arch_coarse N (n-1) u (w i) (ℓ i) hu.1 (hw i hi) (hbase i hi))
        linarith only [hcoarse,hG]
      · have hzero : F u=0 := by
          apply sum_eq_zero
          intro i hi
          have hl : (0:ℝ)<ℓ i := by exact_mod_cast hℓ i hi
          have hv : (n-1-u^2)/(ℓ i:ℝ)∉Set.Icc (2:ℝ) ((N:ℝ)^2) := by
            intro hh
            have hh' := (le_div_iff₀ hl).mp hh.1
            linarith
          simp only [goldbachWeightedArchIntegrand,goldbachLogWindow,Set.indicator_of_notMem hv,
            Complex.zero_re,mul_zero]
        rw [hzero]
        linarith only [hG,hKind]
  have hInt := integral_mono_ae hFi (hGi.add hKi) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hpoint u hu)
  have hbad : (∫ u in Set.Icc (2:ℝ) (N:ℝ),S.indicator (fun _ : ℝ=>K) u)≤
      (2*T/Real.sqrt n)*K := by
    rw [setIntegral_indicator hSm,setIntegral_const,smul_eq_mul]
    have hm := measureReal_mono (μ:=volume)
      (show Set.Icc (2:ℝ) (N:ℝ)∩S⊆S from Set.inter_subset_right) hSfin
    have hs := goldbach_weighted_thin_window_measure n T hn (by linarith) hTn
    exact mul_le_mul_of_nonneg_right (hm.trans hs) hK
  simp only [Pi.add_apply] at hInt
  rw [integral_add hGi hKi] at hInt
  have hGid : (∫ u in Set.Icc (2:ℝ) (N:ℝ),G u)=
      2*B*Real.log N*(goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re := by
    dsimp only [G]
    rw [integral_const_mul,←goldbach_lower_arch_real]
  rw [hGid] at hInt
  rw [goldbach_weighted_arch_sum_identity]
  change (∫ u in Set.Icc (2:ℝ) (N:ℝ),F u)≤_
  dsimp only [K] at hbad
  have he : (2*T/Real.sqrt n)*((∑ i∈I,w i)/(Real.log 2)^3)=
      (2*T/Real.sqrt n)*(∑ i∈I,w i)/(Real.log 2)^3 := by ring
  rw [he] at hbad
  linarith only [hInt,hbad]

end PrimeSquares
