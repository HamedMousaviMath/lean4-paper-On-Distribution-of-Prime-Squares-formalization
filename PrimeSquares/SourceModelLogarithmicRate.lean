import PrimeSquares.MajorArcParameters

/-!
# Explicit logarithmic absorption for the actual source scale R
-/

open Filter
open scoped Topology

namespace PrimeSquares

theorem eventually_exp_neg_rpow_le_power {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c*x^α) ≤ (2 : ℝ)^A * (1+x)^(-A) := by
  have hb := (isLittleO_exp_neg_mul_rpow_atTop hc (-A/α)).bound (by norm_num : (0 : ℝ) < 1)
  have hp := (tendsto_rpow_atTop hα).eventually hb
  filter_upwards [eventually_ge_atTop (1 : ℝ), hp] with x hx h
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x^α := Real.rpow_pos_of_pos hx0 _
  have he : (x^α)^(-A/α) = x^(-A) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  have hraw : Real.exp (-c*x^α) ≤ x^(-A) := by
    have hh : Real.exp (-c*x^α) ≤ (x^α)^(-A/α) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg hxp.le _), one_mul] using h
    rwa [he] at hh
  have hm : (2*x)^(-A) ≤ (1+x)^(-A) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have htwo : (2 : ℝ)^A * (2*x)^(-A) = x^(-A) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le, ← mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul]
  exact hraw.trans (by
    rw [← htwo]
    exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by norm_num) _))

theorem sourceMajorArcScale_inverse_sixth {N Q : ℝ} (hQ : 0 < Q) :
    (sourceMajorArcScale N Q)^(-(1/6 : ℝ)) ≤
      Q^(-(1/2 : ℝ)) * Real.exp (-(5/48 : ℝ)*(Real.log N)^(1/10 : ℝ)) := by
  have hR := sourceMajorArcScale_pos N Q
  have hq : (Q^8)^(-(1/16 : ℝ)) = Q^(-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast Q 8, ← Real.rpow_mul hQ.le]
    norm_num
  have he : (Real.exp ((Real.log N)^(1/10 : ℝ)))^(-(5/48 : ℝ)) =
      Real.exp (-(5/48 : ℝ)*(Real.log N)^(1/10 : ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hsplit : (sourceMajorArcScale N Q)^(-(1/6 : ℝ)) =
      (sourceMajorArcScale N Q)^(-(1/16 : ℝ)) *
      (sourceMajorArcScale N Q)^(-(5/48 : ℝ)) := by
    rw [← Real.rpow_add hR]
    norm_num
  rw [hsplit]
  have hfirst := Real.rpow_le_rpow_of_nonpos (pow_pos hQ 8)
    (le_max_right (Real.exp ((Real.log N)^(1/10 : ℝ))) (Q^8))
    (by norm_num : -(1/16 : ℝ) ≤ 0)
  have hsecond := Real.rpow_le_rpow_of_nonpos
    (Real.exp_pos ((Real.log N)^(1/10 : ℝ)))
    (le_max_left (Real.exp ((Real.log N)^(1/10 : ℝ))) (Q^8))
    (by norm_num : -(5/48 : ℝ) ≤ 0)
  rw [hq] at hfirst
  rw [he] at hsecond
  exact mul_le_mul hfirst hsecond (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hQ.le _)

theorem sourceMajorArcScale_logarithmic_rate {A : ℝ} (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      (sourceMajorArcScale N Q)^(-(1/6 : ℝ)) ≤
        (2 : ℝ)^A * Q^(-(1/2 : ℝ)) * (1+Real.log N)^(-A) := by
  have hreal := Real.tendsto_log_atTop.eventually
    (eventually_exp_neg_rpow_le_power (by norm_num : (0 : ℝ) < 5/48)
      (by norm_num : (0 : ℝ) < 1/10) hA)
  have hnat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually hreal
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hnat
  refine ⟨N₀, ?_⟩
  intro N hN Q hQ
  have hq : 0 < Q := by linarith
  calc
    _ ≤ Q^(-(1/2 : ℝ)) * Real.exp (-(5/48 : ℝ)*(Real.log N)^(1/10 : ℝ)) :=
      sourceMajorArcScale_inverse_sixth hq
    _ ≤ Q^(-(1/2 : ℝ)) * ((2 : ℝ)^A * (1+Real.log N)^(-A)) :=
      mul_le_mul_of_nonneg_left (hN₀ N hN) (Real.rpow_nonneg hq.le _)
    _ = _ := by ring

theorem eventually_affine_log_le_rpow (A B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, A+B*Real.log R ≤ R^ε := by
  have h1 := (tendsto_rpow_neg_atTop hε).const_mul A
  have h2 := ((isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero).const_mul B
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with R hR hb
  have he : A*R^(-ε) + B*(Real.log R/R^ε) = (A+B*Real.log R)/R^ε := by
    rw [Real.rpow_neg hR.le]
    ring
  rw [he] at hb
  simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hR ε)).mp hb.le

theorem eventually_affine_log_model_tail (A B : ℝ) :
    ∀ᶠ R : ℝ in atTop,
      (A+B*Real.log R)*R^(-(5/12 : ℝ)) ≤ R^(-(1/3 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_affine_log_le_rpow A B (by norm_num : (0 : ℝ) < 1/12)] with R hR hb
  calc
    _ ≤ R^(1/12 : ℝ)*R^(-(5/12 : ℝ)) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [← Real.rpow_add hR]; norm_num

end PrimeSquares
