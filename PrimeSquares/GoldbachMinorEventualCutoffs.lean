import PrimeSquares.GoldbachMinorLogParameters
import PrimeSquares.LogPowerAbsorption

set_option autoImplicit false
open Filter
namespace PrimeSquares

/-- All small-scale and proper-prime-power budgets follow from elementary
logarithm versus power limits. The threshold is independent of prime cutoffs. -/
theorem goldbach_minor_real_eventual_budgets (t C T : ℝ) (hT : 0<T) :
    ∀ᶠ x : ℝ in atTop,
      1≤Real.log x ∧ T≤x*(Real.log x)^(-goldbachMinorCutoffExponent t) ∧
      ((Real.log x)^C)^4≤(x*(Real.log x)^(-goldbachMinorCutoffExponent t))/2 ∧
      Real.sqrt x*Real.log x≤x*(Real.log x)^(-t) := by
  let K := goldbachMinorCutoffExponent t
  have hsmall := (isLittleO_log_rpow_rpow_atTop K (by norm_num : (0:ℝ)<1)).bound
    (div_pos (by norm_num : (0:ℝ)<1) hT)
  have hpower := (isLittleO_log_rpow_rpow_atTop (4*C+K) (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1/2)
  have hsqrt := (isLittleO_log_rpow_rpow_atTop (t+1) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop (Real.exp 1),hsmall,hpower,hsqrt] with x hx hs hp he
  have hx0 : 0<x := (Real.exp_pos 1).trans_le hx
  have hl1 : 1≤Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hl0 : 0<Real.log x := by linarith
  have hs' : (Real.log x)^K≤(1/T)*x := by
    simpa only [Real.norm_eq_abs,Real.rpow_one,
      abs_of_nonneg (Real.rpow_nonneg hl0.le _),abs_of_nonneg hx0.le] using hs
  have hp' : (Real.log x)^(4*C+K)≤x/2 := by
    simpa only [Real.norm_eq_abs,Real.rpow_one,
      abs_of_nonneg (Real.rpow_nonneg hl0.le _),abs_of_nonneg hx0.le,one_div_mul_eq_div] using hp
  have he' : (Real.log x)^(t+1)≤x^(1/2:ℝ) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hl0.le _),abs_of_nonneg (Real.rpow_nonneg hx0.le _),one_mul] using he
  refine ⟨hl1,?_,?_,?_⟩
  · have hb : T*(Real.log x)^K≤x := calc
      _≤T*((1/T)*x) := mul_le_mul_of_nonneg_left hs' hT.le
      _=x := by field_simp [hT.ne']
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hl0 K)).mpr hb
    simpa only [div_eq_mul_inv,Real.rpow_neg hl0.le] using hh
  · have hid : ((Real.log x)^C)^4*(Real.log x)^K=(Real.log x)^(4*C+K) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hl0.le,←Real.rpow_add hl0]
      congr 1
      ring
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hl0 K)).mpr (hid.le.trans hp')
    simpa only [div_eq_mul_inv,Real.rpow_neg hl0.le,mul_assoc,mul_comm (2:ℝ)⁻¹] using hh
  · have hh := mul_le_mul_of_nonneg_left he' (Real.sqrt_nonneg x)
    have hsq : Real.sqrt x*x^(1/2:ℝ)=x := by
      rw [←Real.sqrt_eq_rpow,Real.mul_self_sqrt hx0.le]
    have hid : (Real.sqrt x*Real.log x)*(Real.log x)^t=
        Real.sqrt x*(Real.log x)^(t+1) := by
      rw [Real.rpow_add hl0,Real.rpow_one]
      ring
    have hb : (Real.sqrt x*Real.log x)*(Real.log x)^t≤x :=
      hid.le.trans (hh.trans_eq hsq)
    have hh' := (le_div_iff₀ (Real.rpow_pos_of_pos hl0 t)).mpr hb
    simpa only [div_eq_mul_inv,Real.rpow_neg hl0.le] using hh'

theorem goldbach_minor_eventual_numeric_parameters (D : UniformRenGhoshInputs) (t C : ℝ) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧
      4≤(N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t) ∧
      (D.startingScale:ℝ)≤(N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t) ∧
      Real.exp 1≤(N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t) ∧
      ((Real.log N)^C)^4≤((N:ℝ)*(Real.log N)^(-goldbachMinorCutoffExponent t))/2 ∧
      Real.sqrt N*Real.log N≤(N:ℝ)*(Real.log N)^(-t) := by
  let T : ℝ := max 4 (max (D.startingScale:ℝ) (Real.exp 1))
  have hT : 0<T := lt_of_lt_of_le (by norm_num : (0:ℝ)<4) (le_max_left _ _)
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop).eventually
    (goldbach_minor_real_eventual_budgets t C T hT)
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  refine ⟨max M 4,le_max_right _ _,?_⟩
  intro N hN
  obtain ⟨hl,hH,hp,hs⟩ := hM N ((le_max_left _ _).trans hN)
  exact ⟨hl,(le_max_left _ _).trans hH,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hH,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hH,hp,hs⟩

end PrimeSquares
