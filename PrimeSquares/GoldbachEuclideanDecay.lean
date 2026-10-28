import PrimeSquares.GoldbachArithmeticEuler
import PrimeSquares.QuadraticIntegralBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_inverse_log_antitone (U : ℝ) :
    AntitoneOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc 2 U) := by
  intro x hx y _ hxy
  have hxp : 0<x := by linarith [hx.1]
  have hlx : 0<Real.log x := Real.log_pos (by linarith [hx.1])
  simpa only [one_div] using one_div_le_one_div_of_le hlx (Real.log_le_log hxp hxy)

theorem goldbach_quadratic_interval_decay {b γ : ℝ} (hb : 2≤b) (hγ : γ≠0) :
    ‖∫ t in (2:ℝ)..b,quadraticOscillation (-γ) t‖≤
      2*quadraticIntegralConstant/Real.sqrt |γ| := by
  have h1 := quadratic_integral_uniform_bound (by linarith : 0≤b) (neg_ne_zero.mpr hγ)
  have h2 := quadratic_integral_uniform_bound (by norm_num : (0:ℝ)≤2) (neg_ne_zero.mpr hγ)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (quadraticOscillation_intervalIntegrable (-γ) 0 2)
    (quadraticOscillation_intervalIntegrable (-γ) 2 b)
  have hs : (∫ t in (2:ℝ)..b,quadraticOscillation (-γ) t)=
      (∫ t in (0:ℝ)..b,quadraticOscillation (-γ) t)-
        ∫ t in (0:ℝ)..2,quadraticOscillation (-γ) t := by rw [←he];abel
  rw [hs]
  calc
    _≤‖∫ t in (0:ℝ)..b,quadraticOscillation (-γ) t‖+
        ‖∫ t in (0:ℝ)..2,quadraticOscillation (-γ) t‖ := norm_sub_le _ _
    _≤quadraticIntegralConstant/Real.sqrt |γ|+quadraticIntegralConstant/Real.sqrt |γ| := by
      simpa only [abs_neg] using add_le_add h1 h2
    _=_ := by ring

theorem goldbachSquareIntegral_decay {U γ : ℝ} (hU : 2≤U) (hγ : γ≠0) :
    ‖goldbachSquareIntegral U γ‖≤
      (2*quadraticIntegralConstant/Real.log 2)/Real.sqrt |γ| := by
  obtain ⟨ξ,hξ,hξb⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    (f:=fun t : ℝ => (Real.log t)⁻¹) hU (inv_nonneg.mpr (Real.log_pos (by linarith : (1:ℝ)<U)).le)
    (goldbach_inverse_log_antitone U) (quadraticOscillation_intervalIntegrable (-γ) 2 U)
  have hid : (∫ t in (2:ℝ)..U,(Real.log t)⁻¹ • quadraticOscillation (-γ) t)=goldbachSquareIntegral U γ := by
    rw [goldbachSquareIntegral,intervalIntegral.integral_of_le hU]
    congr 1
    funext t
    rw [Complex.real_smul,mul_comm]
  rw [hid] at hξb
  calc
    _≤(Real.log 2)⁻¹*‖∫ t in (2:ℝ)..ξ,quadraticOscillation (-γ) t‖ := hξb
    _≤(Real.log 2)⁻¹*(2*quadraticIntegralConstant/Real.sqrt |γ|) :=
      mul_le_mul_of_nonneg_left (goldbach_quadratic_interval_decay hξ.1 hγ) (by positivity)
    _=_ := by ring

theorem goldbach_linear_interval_decay (a b : ℝ) {β : ℝ} (hβ : β≠0) :
    ‖∫ t in a..b,realFourierPhase (β*t)‖≤1/(Real.pi*|β|) := by
  let c := Complex.ofReal (2*Real.pi*β)*Complex.I
  have hc : c≠0 := by
    dsimp only [c]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by positivity) hβ)) Complex.I_ne_zero
  have hd (t : ℝ) : HasDerivAt (fun x => realFourierPhase (β*x)/c) (realFourierPhase (β*t)) t := by
    convert (goldbach_linear_hasDerivAt β t).div_const c using 1
    change realFourierPhase (β*t)=(realFourierPhase (β*t)*c)/c
    rw [mul_div_cancel_right₀ _ hc]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((realFourierPhase_continuous.comp (show Continuous (fun t : ℝ => β*t) by fun_prop)).intervalIntegrable a b)
  rw [hi,←sub_div,norm_div]
  have hn : ‖c‖=2*Real.pi*|β| := by
    simp only [c,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
      abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤(1+1)/‖c‖ := div_le_div_of_nonneg_right
      (by simpa only [realFourierPhase_norm] using norm_sub_le (realFourierPhase (β*b)) (realFourierPhase (β*a)))
      (norm_nonneg _)
    _=_ := by rw [hn];ring

theorem goldbachLinearIntegral_decay {U β : ℝ} (hU : 2≤U) (hβ : β≠0) :
    ‖goldbachLinearIntegral U β‖≤(1/(Real.pi*Real.log 2))/|β| := by
  have hp : IntervalIntegrable (fun t : ℝ => realFourierPhase (β*t)) volume 2 U :=
    (realFourierPhase_continuous.comp (by fun_prop)).intervalIntegrable 2 U
  obtain ⟨ξ,_,hb⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    (f:=fun t : ℝ => (Real.log t)⁻¹) hU (inv_nonneg.mpr (Real.log_pos (by linarith : (1:ℝ)<U)).le)
    (goldbach_inverse_log_antitone U) hp
  have hid : (∫ t in (2:ℝ)..U,(Real.log t)⁻¹ • realFourierPhase (β*t))=goldbachLinearIntegral U β := by
    rw [goldbachLinearIntegral,intervalIntegral.integral_of_le hU]
    congr 1
    funext t
    rw [Complex.real_smul,mul_comm]
  rw [hid] at hb
  calc
    _≤(Real.log 2)⁻¹*‖∫ t in (2:ℝ)..ξ,realFourierPhase (β*t)‖ := hb
    _≤(Real.log 2)⁻¹*(1/(Real.pi*|β|)) :=
      mul_le_mul_of_nonneg_left (goldbach_linear_interval_decay 2 ξ hβ) (by positivity)
    _=_ := by ring

theorem goldbachLinearSourceIntegral_decay (N ℓ : ℕ) (hℓ : 0<ℓ) {W γ : ℝ}
    (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (hγ : γ≠0) :
    ‖goldbachLinearSourceIntegral N ℓ W γ‖≤(1/(Real.pi*Real.log 2))/((ℓ:ℝ)*|γ|) := by
  rw [goldbach_linear_source_integral N ℓ hℓ W γ]
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  simpa only [abs_mul,abs_of_pos hl] using
    goldbachLinearIntegral_decay (le_min hW hX) (mul_ne_zero hl.ne' hγ)

end PrimeSquares
