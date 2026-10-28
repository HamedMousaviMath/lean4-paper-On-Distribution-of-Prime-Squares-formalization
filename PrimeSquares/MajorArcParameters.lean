import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace PrimeSquares

noncomputable def sourceMajorArcScale (N Q : ℝ) : ℝ :=
  max (Real.exp ((Real.log N)^(1/10 : ℝ))) (Q^8)

theorem sourceMajorArcScale_pos (N Q : ℝ) : 0 < sourceMajorArcScale N Q :=
  (Real.exp_pos _).trans_le (le_max_left _ _)

theorem sourceMajorArcScale_one_le {N : ℝ} (hN : 1 ≤ N) (Q : ℝ) :
    1 ≤ sourceMajorArcScale N Q := by
  apply le_trans _ (le_max_left _ _)
  exact Real.one_le_exp_iff.mpr (Real.rpow_nonneg (Real.log_nonneg hN) _)

theorem sourceMajorArcScale_upper {N Q ε : ℝ} (hQ : 0 < Q)
    (hsmall : (Real.log N)^(1/10 : ℝ) ≤ ε * Real.sqrt (Real.log N))
    (hQlog : 8 * Real.log Q ≤ ε * Real.sqrt (Real.log N)) :
    sourceMajorArcScale N Q ≤ Real.exp (ε * Real.sqrt (Real.log N)) := by
  apply max_le
  · exact Real.exp_le_exp.mpr hsmall
  · have hp : Real.exp (8 * Real.log Q) = Q^8 := by
      simpa [Real.exp_log hQ] using Real.exp_nat_mul (Real.log Q) 8
    rw [← hp]
    exact Real.exp_le_exp.mpr hQlog

theorem sourceMajorArcScale_log_upper {N Q ε : ℝ} (hQ : 0 < Q)
    (hsmall : (Real.log N)^(1/10 : ℝ) ≤ ε * Real.sqrt (Real.log N))
    (hQlog : 8 * Real.log Q ≤ ε * Real.sqrt (Real.log N)) :
    Real.log (sourceMajorArcScale N Q) ≤ ε * Real.sqrt (Real.log N) := by
  have h := Real.log_le_log (sourceMajorArcScale_pos N Q)
    (sourceMajorArcScale_upper hQ hsmall hQlog)
  simpa only [Real.log_exp] using h

theorem eventually_rpow_le_mul_rpow {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x^a ≤ ε * x^b := by
  have hlim : Tendsto (fun x : ℝ => x^(a-b)) atTop (𝓝 0) := by
    rw [show a-b = -(b-a) by ring]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hε)] with x hx h
  rw [Real.rpow_sub hx] at h
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hx b)).mp h.le

theorem eventually_sourceMajorArcScale_log_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (ε/8) * Real.sqrt (Real.log N) →
      Real.log (sourceMajorArcScale N Q) ≤ ε * Real.sqrt (Real.log N) := by
  have hp := Real.tendsto_log_atTop.eventually
    (eventually_rpow_le_mul_rpow (by norm_num : (1/10 : ℝ) < 1/2) hε)
  filter_upwards [hp] with N hN
  intro Q hQ hQlog
  apply sourceMajorArcScale_log_upper (by linarith : 0 < Q)
  · simpa only [← Real.sqrt_eq_rpow] using hN
  · linarith

theorem eventually_majorArc_nonunit_conditions {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ R : ℝ, 0 < R →
      Real.log R ≤ ε * Real.sqrt (Real.log N) →
      Real.log R ≤ Real.log N ∧ R^5 * Real.log N ≤ Real.sqrt N := by
  have hs := Real.tendsto_log_atTop.eventually
    (eventually_rpow_le_mul_rpow (by norm_num : (1/2 : ℝ) < 1)
      (by positivity : (0 : ℝ) < (20*ε)⁻¹))
  have he := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0 : ℝ) < 1/4)).bound (by norm_num : (0 : ℝ) < 1)
  have he' := Real.tendsto_log_atTop.eventually he
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs, he'] with N hN hs he
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs' : Real.sqrt (Real.log N) ≤ (20*ε)⁻¹ * Real.log N := by
    simpa only [Real.rpow_one, ← Real.sqrt_eq_rpow] using hs
  have hsmall : ε * Real.sqrt (Real.log N) ≤ Real.log N / 20 := by
    have h := mul_le_mul_of_nonneg_left hs' hε.le
    have hi : ε * (20*ε)⁻¹ = (1/20 : ℝ) := by field_simp [hε.ne']
    rw [← mul_assoc, hi] at h
    linarith
  have hcap : Real.log N ≤ Real.exp (Real.log N / 4) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hL, Real.exp_pos, mul_comm, div_eq_mul_inv] using he
  intro R hR hlog
  constructor
  · linarith
  · have hp5 : Real.exp (5 * Real.log R) = R^5 := by
      simpa [Real.exp_log hR] using Real.exp_nat_mul (Real.log R) 5
    have hp : R^5 ≤ Real.exp (Real.log N / 4) := by
      rw [← hp5, Real.exp_le_exp]
      linarith
    calc
      R^5 * Real.log N ≤ Real.exp (Real.log N / 4) * Real.exp (Real.log N / 4) :=
        mul_le_mul hp hcap hL (Real.exp_pos _).le
      _ = Real.exp (Real.log N / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0]; congr 1; ring

theorem eventually_sourceMajorArc_conditions {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8) * Real.sqrt (Real.log N) →
      1 ≤ sourceMajorArcScale N Q ∧
      Real.log (sourceMajorArcScale N Q) ≤ Real.log N ∧
      (sourceMajorArcScale N Q)^5 * Real.log N ≤ Real.sqrt N ∧
      7 * Real.log (sourceMajorArcScale N Q) ≤ c * Real.sqrt (Real.log N) := by
  let ε := min (c/7) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_sourceMajorArcScale_log_upper hε,
    eventually_majorArc_nonunit_conditions hε] with N hN hscale hnonunit
  intro Q hQ hQlog
  have hlog := hscale Q hQ hQlog
  obtain ⟨hlogN, hbudget⟩ := hnonunit _ (sourceMajorArcScale_pos N Q) hlog
  refine ⟨sourceMajorArcScale_one_le hN Q, hlogN, hbudget, ?_⟩
  have he : ε ≤ c/7 := min_le_left _ _
  have hm := mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg (Real.log N))
  linarith

end PrimeSquares
