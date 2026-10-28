import PrimeSquares.QuadraticIntegralTail

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def quadraticIntegralConstant : ℝ := 1+3/(4*Real.pi)

theorem quadraticIntegralConstant_one_le : 1 ≤ quadraticIntegralConstant := by
  unfold quadraticIntegralConstant
  have h : (0 : ℝ) ≤ 3/(4*Real.pi) := by positivity
  linarith

theorem quadratic_integral_norm_le_length {a b : ℝ} (hab : a ≤ b) (θ : ℝ) :
    ‖∫ t in a..b, quadraticOscillation θ t‖ ≤ b-a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := quadraticOscillation θ) (C := 1)
    (fun t _ => (quadraticOscillation_norm θ t).le)
  simpa only [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] using h

theorem quadratic_integral_uniform_bound {b θ : ℝ} (hb : 0 ≤ b) (hθ : θ ≠ 0) :
    ‖∫ t in (0 : ℝ)..b, quadraticOscillation θ t‖ ≤
      quadraticIntegralConstant/(Real.sqrt |θ|) := by
  let s := Real.sqrt |θ|
  let a := s⁻¹
  have hs : 0 < s := Real.sqrt_pos.mpr (abs_pos.mpr hθ)
  have ha : 0 < a := inv_pos.mpr hs
  have hs2 : s^2 = |θ| := Real.sq_sqrt (abs_nonneg θ)
  have hc := quadraticIntegralConstant_one_le
  have hbase : a ≤ quadraticIntegralConstant*a := by
    have h := mul_le_mul_of_nonneg_right hc ha.le
    simpa only [one_mul] using h
  by_cases hba : b ≤ a
  · calc
      _ ≤ b := by simpa only [sub_zero] using quadratic_integral_norm_le_length hb θ
      _ ≤ a := hba
      _ ≤ _ := by simpa only [a, div_eq_mul_inv] using hbase
  · have hab : a ≤ b := le_of_not_ge hba
    have htail := quadratic_integral_tail_scaled ha hab θ
    have hd : 0 < 4*Real.pi*|θ| := by positivity
    have htail' : ‖∫ t in a..b, quadraticOscillation θ t‖ ≤ (3/(4*Real.pi))*a := by
      calc
        _ ≤ (3*a⁻¹)/(4*Real.pi*|θ|) := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using htail)
        _ = _ := by rw [←hs2]; dsimp [a]; field_simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (quadraticOscillation_intervalIntegrable θ 0 a) (quadraticOscillation_intervalIntegrable θ a b)
    rw [←hsplit]
    calc
      _ ≤ ‖∫ t in (0 : ℝ)..a, quadraticOscillation θ t‖+
          ‖∫ t in a..b, quadraticOscillation θ t‖ := norm_add_le _ _
      _ ≤ a+(3/(4*Real.pi))*a := add_le_add
        (by simpa only [sub_zero] using quadratic_integral_norm_le_length ha.le θ) htail'
      _ = _ := by unfold quadraticIntegralConstant; dsimp [a, s]; ring

noncomputable def initialQuadraticModel (N : ℕ) (θ : ℝ) : ℂ :=
  Complex.ofReal ((N : ℝ)⁻¹)*(∫ t in (0 : ℝ)..(N : ℝ), quadraticOscillation θ t)

theorem initialQuadraticModel_norm_one {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    ‖initialQuadraticModel N θ‖ ≤ 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [initialQuadraticModel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hNp)]
  have h := mul_le_mul_of_nonneg_left (quadratic_integral_norm_le_length hNp.le θ) (inv_pos.mpr hNp).le
  simpa only [sub_zero, inv_mul_cancel₀ hNp.ne'] using h

theorem initialQuadraticModel_decay {N : ℕ} (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ≠ 0) :
    ‖initialQuadraticModel N θ‖ ≤ quadraticIntegralConstant/((N : ℝ)*Real.sqrt |θ|) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [initialQuadraticModel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hNp)]
  calc
    _ ≤ (N : ℝ)⁻¹*(quadraticIntegralConstant/Real.sqrt |θ|) :=
      mul_le_mul_of_nonneg_left (quadratic_integral_uniform_bound hNp.le hθ) (inv_pos.mpr hNp).le
    _ = _ := by ring

end PrimeSquares
