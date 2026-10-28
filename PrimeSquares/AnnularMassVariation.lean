import PrimeSquares.AnnularSmallFrequencyDifference
import PrimeSquares.AnnularModelDecay

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def annularMassFactor (β : ℝ) : ℝ := (1-(1/2 : ℝ)^β)/β

theorem annularMassFactor_nonneg {β : ℝ} (hβ : 0<β) : 0≤annularMassFactor β := by
  apply div_nonneg _ hβ.le
  exact sub_nonneg.mpr (Real.rpow_le_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num) hβ.le)

theorem annularMassFactor_le_one {β : ℝ} (hβ : 0<β) : annularMassFactor β≤1 := by
  have hlog2 : Real.log (2 : ℝ)≤1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have he : (1/2 : ℝ)^β=Real.exp (-β*Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<1/2)]
    simp only [one_div,Real.log_inv]
    congr 1
    ring
  have h := Real.add_one_le_exp (-β*Real.log 2)
  rw [←he] at h
  apply (div_le_one hβ).mpr
  have hm := mul_le_mul_of_nonneg_left hlog2 hβ.le
  nlinarith

theorem annularMass_formula {N : ℕ} (hN : 1≤N) {β : ℝ} (hβ : 0<β) :
    annularOscillatoryModel N β 0=Complex.ofReal ((N : ℝ)^(β-1)*annularMassFactor β) := by
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  rw [annularOscillatoryModel_zero_explicit hN hβ]
  congr 1
  have hdiv : ((N : ℝ)/2)^β=(N : ℝ)^β*(1/2 : ℝ)^β := by
    rw [div_eq_mul_one_div,Real.mul_rpow hN0.le (by norm_num)]
  have he : (N : ℝ)^(β-1)=(N : ℝ)^β/(N : ℝ) := by
    rw [Real.rpow_sub hN0,Real.rpow_one]
  rw [hdiv,he]
  unfold annularMassFactor
  field_simp

theorem annularMass_re_bounds {N : ℕ} (hN : 1≤N) {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) :
    0≤(annularOscillatoryModel N β 0).re ∧ (annularOscillatoryModel N β 0).re≤1 := by
  rw [annularMass_formula hN hβ0,Complex.ofReal_re]
  have hNr : (1 : ℝ)≤N := by exact_mod_cast hN
  have hp : (N : ℝ)^(β-1)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  exact ⟨mul_nonneg (by positivity) (annularMassFactor_nonneg hβ0),
    (mul_le_mul hp (annularMassFactor_le_one hβ0) (annularMassFactor_nonneg hβ0) (by norm_num)).trans_eq (by ring)⟩

theorem annularMass_re_antitone {N M : ℕ} (hN : 1≤N) (hNM : N≤M)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) :
    (annularOscillatoryModel M β 0).re≤(annularOscillatoryModel N β 0).re := by
  rw [annularMass_formula (hN.trans hNM) hβ0,annularMass_formula hN hβ0,
    Complex.ofReal_re,Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN : (0 : ℝ)<N)
      (by exact_mod_cast hNM) (by linarith)) (annularMassFactor_nonneg hβ0)

theorem annularMass_difference_norm {N M : ℕ} (hN : 1≤N) (hNM : N≤M)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) :
    ‖annularOscillatoryModel M β 0-annularOscillatoryModel N β 0‖=
      (annularOscillatoryModel N β 0).re-(annularOscillatoryModel M β 0).re := by
  have h := annularMass_re_antitone hN hNM hβ0 hβ1
  rw [annularMass_formula (hN.trans hNM) hβ0,annularMass_formula hN hβ0,
    Complex.ofReal_re,Complex.ofReal_re] at h ⊢
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr h)]
  ring

theorem annularMass_dyadic_variation {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) :
    (∑ j∈range J,‖annularOscillatoryModel ((2 : ℕ)^(j+1)) β 0-
      annularOscillatoryModel ((2 : ℕ)^j) β 0‖)≤1 := by
  have he (n : ℕ) : (∑ j∈range n,‖annularOscillatoryModel ((2 : ℕ)^(j+1)) β 0-
      annularOscillatoryModel ((2 : ℕ)^j) β 0‖)=
      (annularOscillatoryModel 1 β 0).re-(annularOscillatoryModel ((2 : ℕ)^n) β 0).re := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,ih,annularMass_difference_norm
        (one_le_pow₀ (by norm_num : 1≤(2 : ℕ)))
        (Nat.pow_le_pow_right (by norm_num) (by omega)) hβ0 hβ1]
      ring
  rw [he]
  have h1 := (annularMass_re_bounds (by norm_num : 1≤(1 : ℕ)) hβ0 hβ1).2
  have hJ := (annularMass_re_bounds (one_le_pow₀ (by norm_num : 1≤(2 : ℕ))) hβ0 hβ1 (N := 2^J)).1
  linarith

end PrimeSquares
