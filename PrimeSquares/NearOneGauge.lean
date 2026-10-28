import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The literal Section 7 gauge. The harmless clamp extends its density
continuously to the negative half-line; on the stated domain t ≥ 0 it
is exactly the printed integrand. No analytic theorem is a hypothesis. -/

open Set MeasureTheory
namespace PrimeSquares

noncomputable def nearOneLog (t : ℝ) : ℝ := Real.log (Real.exp 1 + max 0 t)
noncomputable def nearOneRate (t : ℝ) : ℝ :=
  Real.sqrt (nearOneLog t * Real.log (Real.exp 1 + nearOneLog t))
noncomputable def nearOneDensity (C t : ℝ) : ℝ := Real.exp (C * nearOneRate t)
noncomputable def nearOnePsi (C t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, nearOneDensity C u

theorem nearOneLog_one_le (t : ℝ) : 1 ≤ nearOneLog t := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (le_add_of_nonneg_right (le_max_left 0 t))
  simpa [nearOneLog] using h

theorem nearOneLog_mono : Monotone nearOneLog := by
  intro a b hab
  exact Real.log_le_log (by positivity : 0 < Real.exp 1 + max 0 a)
    (add_le_add le_rfl (max_le_max_left 0 hab))

theorem nearOneRate_nonneg (t : ℝ) : 0 ≤ nearOneRate t := Real.sqrt_nonneg _

theorem nearOneRate_mono : Monotone nearOneRate := by
  intro a b hab
  apply Real.sqrt_le_sqrt
  apply mul_le_mul (nearOneLog_mono hab)
    (Real.log_le_log (by have := nearOneLog_one_le a; positivity)
      (add_le_add le_rfl (nearOneLog_mono hab)))
  · exact Real.log_nonneg (by have := nearOneLog_one_le a; have := Real.add_one_le_exp (1 : ℝ); linarith)
  · linarith [nearOneLog_one_le b]

theorem nearOneDensity_continuous (C : ℝ) : Continuous (nearOneDensity C) := by
  have hL : Continuous nearOneLog := by
    apply Continuous.log (continuous_const.add (continuous_const.max continuous_id))
    intro t
    change Real.exp 1 + max 0 t ≠ 0
    exact ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos 1) (le_max_left 0 t))
  have hLL : Continuous (fun t => Real.log (Real.exp 1 + nearOneLog t)) := by
    apply Continuous.log (continuous_const.add hL)
    intro t
    have := nearOneLog_one_le t
    change Real.exp 1 + nearOneLog t ≠ 0
    exact ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos 1) (by linarith))
  unfold nearOneDensity nearOneRate
  exact (continuous_const.mul ((hL.mul hLL).sqrt)).rexp

theorem nearOneDensity_pos (C t : ℝ) : 0 < nearOneDensity C t := Real.exp_pos _

theorem nearOneDensity_one_le {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    1 ≤ nearOneDensity C t := Real.one_le_exp (mul_nonneg hC (nearOneRate_nonneg t))

theorem nearOneDensity_mono {C : ℝ} (hC : 0 ≤ C) : Monotone (nearOneDensity C) := by
  intro a b hab
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (nearOneRate_mono hab) hC)

theorem nearOnePsi_zero (C : ℝ) : nearOnePsi C 0 = 0 := by simp [nearOnePsi]

theorem nearOnePsi_nonneg (C : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ nearOnePsi C t :=
  intervalIntegral.integral_nonneg_of_forall ht (fun u => (nearOneDensity_pos C u).le)

theorem nearOnePsi_hasDerivAt (C t : ℝ) :
    HasDerivAt (nearOnePsi C) (nearOneDensity C t) t := by
  have hc := nearOneDensity_continuous C
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem nearOnePsi_continuous (C : ℝ) : Continuous (nearOnePsi C) := by
  have h : Differentiable ℝ (nearOnePsi C) := fun t => (nearOnePsi_hasDerivAt C t).differentiableAt
  exact h.continuous

theorem nearOnePsi_mono (C : ℝ) : Monotone (nearOnePsi C) := by
  apply monotone_of_deriv_nonneg (fun t => (nearOnePsi_hasDerivAt C t).differentiableAt)
  intro t
  rw [(nearOnePsi_hasDerivAt C t).deriv]
  exact (nearOneDensity_pos C t).le

theorem nearOnePsi_convex {C : ℝ} (hC : 0 ≤ C) : ConvexOn ℝ univ (nearOnePsi C) := by
  apply MonotoneOn.convexOn_of_deriv convex_univ (nearOnePsi_continuous C).continuousOn
    (fun t _ => (nearOnePsi_hasDerivAt C t).differentiableAt.differentiableWithinAt)
  intro a _ b _ hab
  simpa only [(nearOnePsi_hasDerivAt C a).deriv, (nearOnePsi_hasDerivAt C b).deriv]
    using nearOneDensity_mono hC hab

theorem nearOnePsi_ge_self {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) : t ≤ nearOnePsi C t := by
  have h := intervalIntegral.integral_mono_on ht (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t)
    ((nearOneDensity_continuous C).intervalIntegrable 0 t)
    (fun u _ => nearOneDensity_one_le hC u)
  simpa [nearOnePsi] using h

theorem nearOnePsi_le_density {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    nearOnePsi C t ≤ t * nearOneDensity C t := by
  have h := intervalIntegral.integral_mono_on ht ((nearOneDensity_continuous C).intervalIntegrable 0 t)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => nearOneDensity C t) volume 0 t)
    (fun u hu => nearOneDensity_mono hC hu.2)
  simpa [nearOnePsi] using h

theorem nearOneGauge_literal {t : ℝ} (ht : 0 ≤ t) (C : ℝ) :
    nearOneDensity C t = Real.exp (C * Real.sqrt
      (Real.log (Real.exp 1+t) * Real.log (Real.exp 1+Real.log (Real.exp 1+t)))) := by
  simp [nearOneDensity, nearOneRate, nearOneLog, max_eq_right ht]

end PrimeSquares
