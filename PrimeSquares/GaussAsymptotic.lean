import PrimeSquares.GaussLogBound

/-!
# Conditional sharp principal Gauss-sum bound (Lemma 3.21)

The two analytic hypotheses below are precisely stated standard consequences
of PNT. They are hypotheses, not axioms or established results in this project.
All prime-factor estimates and their connection to the actual Gauss sum are
proved here or in the imported finite arithmetic modules.
-/

open Finset Filter Topology

namespace PrimeSquares

noncomputable def gaussAsymptoticScale (y : ℝ) : ℝ := Real.sqrt y / Real.log y

/-- The external analytic boundary: PNT in theta form and its weighted
partial-summation consequence. The bridge from a separately formalized PNT is
not included in this checkpoint. -/
structure PrimeAsymptoticInputs : Prop where
  theta : Tendsto (fun y : ℝ => primeTheta y / y) atTop (𝓝 1)
  invSqrt : Tendsto (fun y : ℝ => primeInvSqrtSum y / gaussAsymptoticScale y) atTop (𝓝 2)

noncomputable def gaussLogCorrection (y : ℝ) : ℝ :=
  Real.log 4 + 4 * (1 + Real.log y + (Real.log 2)⁻¹)

noncomputable def gaussAnalyticMajorant (y : ℝ) : ℝ :=
  primeInvSqrtSum y + (y - primeTheta y) / (Real.sqrt y * Real.log y) + gaussLogCorrection y

theorem gaussAsymptoticScale_pos {y : ℝ} (hy : 1 < y) :
    0 < gaussAsymptoticScale y :=
  div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos hy)

theorem gaussLogCorrection_ratio_tendsto :
    Tendsto (fun y : ℝ => gaussLogCorrection y / gaussAsymptoticScale y) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun y : ℝ => Real.log y ^ 2 / Real.sqrt y) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have h := (h2.const_mul 4).add (h1.const_mul (Real.log 4 + 4 * (1 + (Real.log 2)⁻¹)))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  dsimp [gaussLogCorrection, gaussAsymptoticScale]
  field_simp
  ring

theorem gaussAnalyticMajorant_ratio_tendsto (H : PrimeAsymptoticInputs) :
    Tendsto (fun y : ℝ => gaussAnalyticMajorant y / gaussAsymptoticScale y) atTop (𝓝 2) := by
  have ht : Tendsto (fun y : ℝ => 1 - primeTheta y / y) atTop (𝓝 (1 - 1 : ℝ)) :=
    tendsto_const_nhds.sub H.theta
  have h := (H.invSqrt.add ht).add gaussLogCorrection_ratio_tendsto
  norm_num only [sub_self, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  have hy0 : y ≠ 0 := by linarith
  have hs : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hl : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hs2 := Real.sq_sqrt (show 0 ≤ y by linarith)
  dsimp [gaussAnalyticMajorant, gaussAsymptoticScale]
  field_simp [hy0, hs, hl]
  have he := congrArg (fun t : ℝ => t * (y - primeTheta y)) hs2
  nlinarith only [he]

theorem log_four_mul_gaussOddProduct_le_majorant (q : ℕ) (hq : 0 < q)
    (hL : 2 ≤ Real.log q) :
    Real.log (4 * gaussOddProduct q) ≤ gaussAnalyticMajorant (Real.log q) := by
  have h := log_four_mul_gaussOddProduct_bound q hq hL
  dsimp [gaussAnalyticMajorant, gaussLogCorrection]
  linarith

/-- This bound is unconditional: the analytic inputs are only needed to
identify the limiting leading coefficient of its explicit exponent. -/
theorem principalSquareSum_exp_majorant (q : ℕ) [NeZero q]
    (hL : 2 ≤ Real.log q) (a : ZMod q) (ha : IsUnit a) :
    ‖principalSquareSum q a‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
      Real.exp (gaussAnalyticMajorant (Real.log q)) := by
  have hp : 0 < 4 * gaussOddProduct q := mul_pos (by norm_num)
    (prod_pos fun p hp => gaussOddPrimeFactor_pos p (le_of_lt (mem_filter.mp hp).2))
  have he := Real.exp_le_exp.mpr (log_four_mul_gaussOddProduct_le_majorant q (NeZero.pos q) hL)
  rw [Real.exp_log hp] at he
  calc
    _ ≤ (4 / Real.sqrt q) * gaussOddProduct q := principalSquareSum_finite_product_bound q a ha
    _ = (4 * gaussOddProduct q) / Real.sqrt q := by ring
    _ ≤ Real.exp (gaussAnalyticMajorant (Real.log q)) / Real.sqrt q :=
      div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)
    _ = _ := by ring

noncomputable def gaussAsymptoticError (q : ℕ) : ℝ :=
  gaussAnalyticMajorant (Real.log q) / gaussAsymptoticScale (Real.log q) - 2

theorem gaussAsymptoticError_tendsto (H : PrimeAsymptoticInputs) :
    Tendsto gaussAsymptoticError atTop (𝓝 0) := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h : Tendsto gaussAsymptoticError atTop (𝓝 (2 - 2 : ℝ)) :=
    ((gaussAnalyticMajorant_ratio_tendsto H).comp hlog).sub tendsto_const_nhds
  simpa only [sub_self] using h

/-- Literal 2+o(1) form: this inequality is unconditional, while the displayed
error's convergence to zero is the preceding conditional theorem. -/
theorem principalSquareSum_sharp_error_bound (q : ℕ) [NeZero q]
    (hL : 2 ≤ Real.log q) (a : ZMod q) (ha : IsUnit a) :
    ‖principalSquareSum q a‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
      Real.exp ((2 + gaussAsymptoticError q) * gaussAsymptoticScale (Real.log q)) := by
  have hs : gaussAsymptoticScale (Real.log q) ≠ 0 :=
    ne_of_gt (gaussAsymptoticScale_pos (by linarith))
  have he : (2 + gaussAsymptoticError q) * gaussAsymptoticScale (Real.log q) =
      gaussAnalyticMajorant (Real.log q) := by
    dsimp [gaussAsymptoticError]
    field_simp
    ring
  rw [he]
  exact principalSquareSum_exp_majorant q hL a ha

/-- The paper's literal 2+o(1) statement with one error function independent
of the integer unit coefficient. -/
theorem principalSquareSum_two_add_o_one (H : PrimeAsymptoticInputs) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ (q : ℕ) [NeZero q], 2 ≤ Real.log q → ∀ a : ℤ, IsCoprime (q : ℤ) a →
        ‖principalSquareSum q (a : ZMod q)‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
          Real.exp ((2 + r q) * (Real.sqrt (Real.log q) / Real.log (Real.log q))) := by
  refine ⟨gaussAsymptoticError, gaussAsymptoticError_tendsto H, ?_⟩
  intro q inst hq a ha
  exact principalSquareSum_sharp_error_bound q hq (a : ZMod q)
    ((ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha)

/-- Full epsilon formulation of the sharp upper bound, uniform in a. -/
theorem principalSquareSum_sharp_eventually (H : PrimeAsymptoticInputs)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ [NeZero q] (a : ZMod q), IsUnit a →
      ‖principalSquareSum q a‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
        Real.exp ((2 + ε) * gaussAsymptoticScale (Real.log q)) := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (gaussAnalyticMajorant_ratio_tendsto H).comp hlog
  have he : ∀ᶠ q : ℕ in atTop,
      gaussAnalyticMajorant (Real.log q) / gaussAsymptoticScale (Real.log q) < 2 + ε :=
    hlim.eventually (eventually_lt_nhds (show (2 : ℝ) < 2 + ε by linarith))
  filter_upwards [he, hlog.eventually (eventually_ge_atTop 2)] with q he hqlog
  intro inst a ha
  have hq : 0 < q := NeZero.pos q
  have hs : 0 < gaussAsymptoticScale (Real.log q) :=
    gaussAsymptoticScale_pos (by linarith)
  have hm : gaussAnalyticMajorant (Real.log q) ≤
      (2 + ε) * gaussAsymptoticScale (Real.log q) :=
    (div_le_iff₀ hs).mp he.le
  exact (principalSquareSum_exp_majorant q hqlog a ha).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (inv_nonneg.mpr (Real.sqrt_nonneg _)))

theorem principalSquareSum_three_eventually (H : PrimeAsymptoticInputs) :
    ∀ᶠ q : ℕ in atTop, ∀ [NeZero q] (a : ZMod q), IsUnit a →
      ‖principalSquareSum q a‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
        Real.exp (3 * gaussAsymptoticScale (Real.log q)) := by
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using
    principalSquareSum_sharp_eventually H 1 (by norm_num)

theorem principalSquareSum_sharp_bound_int (H : PrimeAsymptoticInputs)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q], Q ≤ q → ∀ a : ℤ, IsCoprime (q : ℤ) a →
      ‖principalSquareSum q (a : ZMod q)‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
        Real.exp ((2 + ε) * (Real.sqrt (Real.log q) / Real.log (Real.log q))) := by
  obtain ⟨Q, hQ⟩ := (principalSquareSum_sharp_eventually H ε hε).exists_forall_of_atTop
  refine ⟨Q, ?_⟩
  intro q inst hq a ha
  exact hQ q hq (a : ZMod q) ((ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha)

theorem principalSquareSum_three_bound_int (H : PrimeAsymptoticInputs) :
    ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q], Q ≤ q → ∀ a : ℤ, IsCoprime (q : ℤ) a →
      ‖principalSquareSum q (a : ZMod q)‖ ≤ (Real.sqrt (q : ℝ))⁻¹ *
        Real.exp (3 * (Real.sqrt (Real.log q) / Real.log (Real.log q))) := by
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using
    principalSquareSum_sharp_bound_int H 1 (by norm_num)

end PrimeSquares
