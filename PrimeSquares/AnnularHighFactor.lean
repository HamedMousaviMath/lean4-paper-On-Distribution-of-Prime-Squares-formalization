import PrimeSquares.AnnularHighMask
import PrimeSquares.AnnularModelDecay

namespace PrimeSquares

noncomputable def highMaskConstant : ℝ := 1+4/Real.pi

theorem highMaskConstant_one_le : 1 ≤ highMaskConstant :=
  le_add_of_nonneg_right (div_nonneg (by norm_num) Real.pi_pos.le)

noncomputable def annularHighFactor (N : ℕ) (β q W θ : ℝ) : ℂ :=
  annularOscillatoryModel N β θ*Complex.ofReal (annularHighMask N q W θ)

theorem annularHighFactor_le_annular (N : ℕ) (β q W θ : ℝ) :
    ‖annularHighFactor N β q W θ‖ ≤ ‖annularOscillatoryModel N β θ‖ := by
  rw [annularHighFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annularHighMask_range N q W θ).1]
  exact (mul_le_mul_of_nonneg_left (annularHighMask_range N q W θ).2 (norm_nonneg _)).trans (by simp)

theorem annularHighFactor_half {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : β ≤ 1) (q W θ : ℝ) :
    ‖annularHighFactor N β q W θ‖ ≤ 1/2 :=
  (annularHighFactor_le_annular N β q W θ).trans (annularOscillatoryModel_norm_half hN hβ θ)

theorem annularHighFactor_linear {N : ℕ} (hN : 2 ≤ N) {β q W : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq : 0 < q) (hW : 0 < W) (θ : ℝ) :
    ‖annularHighFactor N β q W θ‖ ≤ highMaskConstant*q/W := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hC := highMaskConstant_one_le
  by_cases hql : q ≤ W
  · by_cases hz : annularHighMask N q W θ=0
    · simp only [annularHighFactor,hz,Complex.ofReal_zero,mul_zero,norm_zero]
      exact div_nonneg (mul_nonneg (by linarith) hq.le) hW.le
    · have ho := annularHighMask_onset hNp hq hW hql hz
      have hb := annularOscillatoryModel_outside_arc (N := N) (β := β) (q := 2*q) (R := W)
        hN hβ0 hβ1 (by positivity) hW (by simpa only [mul_assoc] using ho.le)
      calc
        _ ≤ _ := (annularHighFactor_le_annular N β q W θ).trans hb
        _ = (4/Real.pi)*(q/W) := by ring
        _ ≤ highMaskConstant*(q/W) := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)) (div_nonneg hq.le hW.le)
        _ = _ := by ring
  · have hratio : 1 ≤ q/W := (one_le_div hW).mpr (le_of_not_ge hql)
    have hprod : 1 ≤ highMaskConstant*(q/W) := one_le_mul_of_one_le_of_one_le hC hratio
    have hs := annularHighFactor_half hN hβ1 q W θ
    calc
      _ ≤ 1/2 := hs
      _ ≤ highMaskConstant*(q/W) := (by norm_num : (1/2 : ℝ) ≤ 1).trans hprod
      _ = _ := by ring

end PrimeSquares
