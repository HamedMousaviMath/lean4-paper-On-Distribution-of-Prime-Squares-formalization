import PrimeSquares.GoldbachWeightedIntegralConstant

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_inner_mellin (D r : ℝ) (hD : 0<D) (_hr0 : 0≤r) (hr1 : r≤1/9) :
    (∫ p in Real.exp ((4/9:ℝ)*D)..Real.exp (D*(1-r)/2),
      1/(p*Real.log p*(D-D*r-Real.log p)^2))=
        (1/D^2)*goldbachWeightedInnerIntegral r := by
  let f := fun v : ℝ=>Real.exp (D*v)
  let f' := fun v : ℝ=>D*Real.exp (D*v)
  let g := fun p : ℝ=>1/(p*Real.log p*(D-D*r-Real.log p)^2)
  have hab : (4/9:ℝ)≤(1-r)/2 := by linarith
  have hf : ∀ v∈Set.uIcc (4/9:ℝ) ((1-r)/2),HasDerivAt f (f' v) v := by
    intro v hv
    convert ((hasDerivAt_id v).const_mul D).exp using 1
    · rfl
    · dsimp only [f',id_eq];ring
  have hf' : ContinuousOn f' (Set.uIcc (4/9:ℝ) ((1-r)/2)) := by
    dsimp only [f']
    fun_prop
  have hg : ContinuousOn g (f '' Set.uIcc (4/9:ℝ) ((1-r)/2)) := by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := hp
    rw [Set.uIcc_of_le hab] at hv
    have hv0 : 0<v := by linarith [hv.1]
    have hp0 : f v≠0 := (Real.exp_pos _).ne'
    have hlog : Real.log (f v)≠0 := by
      dsimp only [f]
      rw [Real.log_exp]
      exact (mul_pos hD hv0).ne'
    have hL : D-D*r-Real.log (f v)≠0 := by
      dsimp only [f]
      rw [Real.log_exp]
      have hh : 0<D*(1-r-v) := mul_pos hD (by linarith [hv.2])
      nlinarith only [hh]
    have hden : f v*Real.log (f v)*(D-D*r-Real.log (f v))^2≠0 :=
      mul_ne_zero (mul_ne_zero hp0 hlog) (pow_ne_zero 2 hL)
    apply ContinuousAt.continuousWithinAt
    dsimp only [g]
    fun_prop
  have hsub := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  have hends : f (4/9:ℝ)=Real.exp ((4/9:ℝ)*D) ∧
      f ((1-r)/2)=Real.exp (D*(1-r)/2) := by
    constructor <;> dsimp only [f] <;> congr 1 <;> ring
  rw [hends.1,hends.2] at hsub
  rw [←hsub,goldbachWeightedInnerIntegral,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hab] at hv
  have hv0 : v≠0 := by linarith [hv.1]
  have hs : 1-r-v≠0 := by linarith [hv.2]
  have hL : D-D*r-D*v≠0 := by
    have hh : 0<D*(1-r-v) := mul_pos hD (by linarith [hv.2])
    nlinarith only [hh]
  dsimp only [Function.comp_apply,f,f',g]
  rw [Real.log_exp]
  have he := (Real.exp_pos (D*v)).ne'
  field_simp

theorem goldbach_weighted_outer_mellin (D r₀ : ℝ) (hD : 0<D) (hr0 : 0<r₀) (hr1 : r₀≤1/9) :
    (∫ u in (Real.exp (D*r₀)/2)..(Real.exp (D/9)/2),
      goldbachWeightedInnerIntegral (Real.log (2*u)/D)/(u*Real.sqrt (Real.log (2*u))))=
      Real.sqrt D*(∫ r in r₀..(1/9:ℝ),goldbachWeightedInnerIntegral r/Real.sqrt r) := by
  let f := fun r : ℝ=>Real.exp (D*r)/2
  let f' := fun r : ℝ=>D*Real.exp (D*r)/2
  let g := fun u : ℝ=>goldbachWeightedInnerIntegral (Real.log (2*u)/D)/(u*Real.sqrt (Real.log (2*u)))
  have hf : ∀ r∈Set.uIcc r₀ (1/9:ℝ),HasDerivAt f (f' r) r := by
    intro r hr
    convert (((hasDerivAt_id r).const_mul D).exp).div_const 2 using 1
    · rfl
    · dsimp only [f',id_eq];ring
  have hf' : ContinuousOn f' (Set.uIcc r₀ (1/9:ℝ)) := by
    dsimp only [f']
    fun_prop
  let S := f '' Set.uIcc r₀ (1/9:ℝ)
  have hrange : ∀ u∈S,0<u ∧ 0<Real.log (2*u) ∧
      Real.log (2*u)/D∈Set.Icc (0:ℝ) (1/9:ℝ) := by
    intro u hu
    obtain ⟨r,hr,rfl⟩ := hu
    rw [Set.uIcc_of_le hr1] at hr
    have he : 2*f r=Real.exp (D*r) := by dsimp only [f];ring
    have hlog : Real.log (2*f r)=D*r := by rw [he,Real.log_exp]
    have hrpos : 0<r := hr0.trans_le hr.1
    refine ⟨by dsimp only [f];positivity,by rw [hlog];exact mul_pos hD hrpos,?_⟩
    rw [hlog,mul_div_cancel_left₀ _ hD.ne']
    exact ⟨hrpos.le,hr.2⟩
  have hg : ContinuousOn g S := by
    have hm : ContinuousOn (fun u : ℝ=>Real.log (2*u)/D) S := by
      intro u hu
      have hu0 : 2*u≠0 := mul_ne_zero (by norm_num) (hrange u hu).1.ne'
      apply ContinuousAt.continuousWithinAt
      fun_prop
    have hJ := goldbach_weighted_inner_continuous.comp hm (fun u hu=>(hrange u hu).2.2)
    have hden : ContinuousOn (fun u : ℝ=>1/(u*Real.sqrt (Real.log (2*u)))) S := by
      intro u hu
      have hu0 := (hrange u hu).1.ne'
      have h₂ : 2*u≠0 := mul_ne_zero (by norm_num) hu0
      have hs : Real.sqrt (Real.log (2*u))≠0 := (Real.sqrt_pos.mpr (hrange u hu).2.1).ne'
      have hd := mul_ne_zero hu0 hs
      apply ContinuousAt.continuousWithinAt
      fun_prop
    have hh := hJ.mul hden
    apply hh.congr
    intro u hu
    dsimp only [g,Pi.mul_apply,Function.comp_apply]
    ring
  have hsub := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  have hlast : f (1/9:ℝ)=Real.exp (D/9)/2 := by dsimp only [f];congr 2;ring
  rw [hlast] at hsub
  rw [←hsub,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le hr1] at hr
  have hrpos : 0<r := hr0.trans_le hr.1
  have hlog : Real.log (2*f r)=D*r := by
    rw [show 2*f r=Real.exp (D*r) by dsimp only [f];ring,Real.log_exp]
  dsimp only [Function.comp_apply,g]
  rw [hlog,mul_div_cancel_left₀ _ hD.ne',Real.sqrt_mul hD.le]
  dsimp only [f,f']
  have he := (Real.exp_pos (D*r)).ne'
  have hsD := (Real.sqrt_pos.mpr hD).ne'
  have hsr := (Real.sqrt_pos.mpr hrpos).ne'
  field_simp
  rw [Real.sq_sqrt hD.le]

theorem goldbach_weighted_outer_mellin_le_W (D r₀ : ℝ) (hD : 0<D) (hr0 : 0<r₀) (hr1 : r₀≤1/9) :
    (∫ u in (Real.exp (D*r₀)/2)..(Real.exp (D/9)/2),
      goldbachWeightedInnerIntegral (Real.log (2*u)/D)/(u*Real.sqrt (Real.log (2*u))))≤
      Real.sqrt D*(8*Real.sqrt 2*goldbachWeightedW (9/8)) := by
  rw [goldbach_weighted_outer_mellin D r₀ hD hr0 hr1,←goldbach_weighted_W_identity]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg D)
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤1/9)).mp
    goldbach_weighted_outer_integrable
  have hs : Set.Icc r₀ (1/9:ℝ)⊆Set.Icc (0:ℝ) (1/9:ℝ) := Set.Icc_subset_Icc hr0.le le_rfl
  have hh := setIntegral_mono_set hi
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact div_nonneg (goldbach_weighted_inner_nonneg r hr.2) (Real.sqrt_nonneg r)) hs.eventuallyLE
  change (∫ r in Set.Icc r₀ (1/9:ℝ),goldbachWeightedInnerIntegral r/Real.sqrt r)≤
    ∫ r in Set.Icc (0:ℝ) (1/9:ℝ),goldbachWeightedInnerIntegral r/Real.sqrt r at hh
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc] at hh
  simpa only [intervalIntegral.integral_of_le hr1,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/9)] using hh

end PrimeSquares
