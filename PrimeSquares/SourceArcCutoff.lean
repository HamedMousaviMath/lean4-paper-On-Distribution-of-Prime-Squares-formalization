import PrimeSquares.RationalArcSeparation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# An actual even smooth cutoff and the geometry of its dyadic dilates
-/

open scoped ContDiff

namespace PrimeSquares

noncomputable def sourceArcBump : ContDiffBump (0 : ℝ) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

noncomputable def sourceArcCutoff (θ : ℝ) : ℝ := sourceArcBump θ

noncomputable def sourceArcCutoffScale (s : ℕ) (θ : ℝ) : ℝ :=
  sourceArcCutoff ((16 : ℝ)^s * θ)

theorem sourceArcCutoff_contDiff : ContDiff ℝ ∞ sourceArcCutoff :=
  sourceArcBump.contDiff

theorem sourceArcCutoff_even (θ : ℝ) : sourceArcCutoff (-θ) = sourceArcCutoff θ :=
  sourceArcBump.neg θ

theorem sourceArcCutoff_nonneg (θ : ℝ) : 0 ≤ sourceArcCutoff θ :=
  sourceArcBump.nonneg

theorem sourceArcCutoff_le_one (θ : ℝ) : sourceArcCutoff θ ≤ 1 :=
  sourceArcBump.le_one

theorem sourceArcCutoff_core {θ : ℝ} (hθ : |θ| ≤ 1/2) : sourceArcCutoff θ = 1 := by
  apply sourceArcBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sourceArcBump] using hθ

theorem sourceArcCutoff_zero {θ : ℝ} (hθ : 1 ≤ |θ|) : sourceArcCutoff θ = 0 := by
  apply sourceArcBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, sourceArcBump] using hθ

theorem sourceArcCutoff_radius {θ : ℝ} (hθ : sourceArcCutoff θ ≠ 0) : |θ| < 1 := by
  by_contra h
  exact hθ (sourceArcCutoff_zero (le_of_not_gt h))

theorem sourceArcCutoffScale_radius (s : ℕ) {θ : ℝ}
    (hθ : sourceArcCutoffScale s θ ≠ 0) : |θ| < 1 / (16 : ℝ)^s := by
  have hp : (0 : ℝ) < (16 : ℝ)^s := by positivity
  have h := sourceArcCutoff_radius hθ
  rw [abs_mul, abs_of_pos hp] at h
  exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)

theorem sourceArcCutoffScale_core (s : ℕ) {θ : ℝ}
    (hθ : |θ| ≤ 1 / (2 * (16 : ℝ)^s)) : sourceArcCutoffScale s θ = 1 := by
  apply sourceArcCutoff_core
  have hp : (0 : ℝ) < (16 : ℝ)^s := by positivity
  have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hp)).mp hθ
  rw [abs_mul, abs_of_pos hp]
  nlinarith only [h]

theorem dyadic_sixteen_scale (s : ℕ) : (16 : ℝ)^s = ((2 : ℝ)^s)^4 := by
  rw [show (16 : ℝ) = 2^4 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 4 s]

theorem sourceArcCutoffScale_major_arc {N q R θ : ℝ} {s : ℕ}
    (hN : 0 < N) (hq : 0 < q) (hqR : q ≤ R) (hs : (2 : ℝ)^s ≤ q)
    (hbudget : 2*R^4 ≤ N^2) (hθ : |θ| ≤ R/(q*N^2)) :
    sourceArcCutoffScale s θ = 1 := by
  have hR : 0 < R := hq.trans_le hqR
  have hscale : (16 : ℝ)^s ≤ q^4 := by
    rw [dyadic_sixteen_scale]
    exact pow_le_pow_left₀ (by positivity) hs 4
  have hq3 : q^3 ≤ R^3 := pow_le_pow_left₀ hq.le hqR 3
  apply sourceArcCutoff_core
  change |(16 : ℝ)^s * θ| ≤ 1/2
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (16 : ℝ)^s)]
  calc
    (16 : ℝ)^s * |θ| ≤ q^4 * |θ| :=
      mul_le_mul_of_nonneg_right hscale (abs_nonneg _)
    _ ≤ q^4 * (R/(q*N^2)) := mul_le_mul_of_nonneg_left hθ (by positivity)
    _ = q^3*R/N^2 := by field_simp
    _ ≤ R^3*R/N^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq3 hR.le) (sq_nonneg N)
    _ = R^4/N^2 := by ring
    _ ≤ 1/2 := (div_le_iff₀ (sq_pos_of_pos hN)).mpr (by linarith)

theorem dyadic_cutoff_width {s : ℕ} (hs : 2 ≤ s) :
    2 * (1 / (16 : ℝ)^s) < 1 / ((2 : ℝ)^(s+1))^2 := by
  have hnat : 4 ≤ 2^s := by
    calc
      4 = 2^2 := by norm_num
      _ ≤ 2^s := Nat.pow_le_pow_right (by norm_num) hs
  have hA : (4 : ℝ) ≤ (2 : ℝ)^s := by exact_mod_cast hnat
  have hApos : (0 : ℝ) < (2 : ℝ)^s := by positivity
  rw [dyadic_sixteen_scale,
    show (2 : ℝ)^(s+1) = (2 : ℝ)^s * 2 from pow_succ _ _]
  have hA2 : 8 < ((2 : ℝ)^s)^2 := by nlinarith only [hA]
  have hh := mul_lt_mul_of_pos_right hA2 (sq_pos_of_pos hApos)
  rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hh]

theorem sourceArcCutoffScale_unique {s : ℕ} (hs : 2 ≤ s) {r t : ℚ} {ξ : ℝ}
    (hr : (r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (ht : (t.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (har : sourceArcCutoffScale s (ξ-(r : ℝ)) ≠ 0)
    (hat : sourceArcCutoffScale s (ξ-(t : ℝ)) ≠ 0) : r = t :=
  rational_small_arc_unique hr ht (dyadic_cutoff_width hs)
    (sourceArcCutoffScale_radius s har).le (sourceArcCutoffScale_radius s hat).le

end PrimeSquares
