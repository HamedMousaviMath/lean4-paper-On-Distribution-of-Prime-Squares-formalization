import PrimeSquares.IWStartingScaleBudget
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwNarrowWidth (ε : ℝ) (P : ℕ) : ℝ := min (ε/16) (1/(100*(P : ℝ)))

theorem iwNarrowWidth_pos {ε : ℝ} (hε : 0<ε) {P : ℕ} (hP : 1≤ P) :
    0< iwNarrowWidth ε P := by
  have hPr : (0 : ℝ)< P := by exact_mod_cast hP
  unfold iwNarrowWidth
  positivity

theorem iwNarrowWidth_le_original (ε : ℝ) (P : ℕ) : iwNarrowWidth ε P≤ε/16 := min_le_left _ _

theorem iwNarrowWidth_le_period (ε : ℝ) (P : ℕ) : iwNarrowWidth ε P≤1/(100*(P : ℝ)) := min_le_right _ _

theorem iwNarrowWidth_small (ε : ℝ) {P : ℕ} (hP : 1≤ P) : iwNarrowWidth ε P≤1/100 := by
  have hPr : (1 : ℝ)≤ P := by exact_mod_cast hP
  apply (iwNarrowWidth_le_period ε P).trans
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<100)
  linarith

theorem iwNarrowWidth_cutoff_core {ε : ℝ} (hε : 0<ε) {P : ℕ} {θ : ℝ}
    (hθ : |θ|≤ iwNarrowWidth ε P) : sourceArcCutoff (θ/ε)=1 := by
  apply sourceArcCutoff_core
  rw [abs_div,abs_of_pos hε]
  apply (div_le_iff₀ hε).mpr
  have hb := hθ.trans (iwNarrowWidth_le_original ε P)
  linarith

theorem iwNarrowWidth_log_inverse {ε : ℝ} (hε : 0<ε) {P : ℕ} (hP : 1≤ P) :
    -Real.log (iwNarrowWidth ε P)≤
      max (Real.log 16-Real.log ε) (Real.log 100+Real.log (P : ℝ)) := by
  have hPr : (0 : ℝ)< P := by exact_mod_cast hP
  unfold iwNarrowWidth
  by_cases h : ε/16≤1/(100*(P : ℝ))
  · rw [min_eq_left h,Real.log_div hε.ne' (by norm_num : (16 : ℝ)≠0)]
    have he : -(Real.log ε-Real.log 16)=Real.log 16-Real.log ε := by ring
    rw [he]
    exact le_max_left _ _
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),one_div,Real.log_inv,
      Real.log_mul (by norm_num : (100 : ℝ)≠0) hPr.ne',neg_neg]
    exact le_max_right _ _

end PrimeSquares
