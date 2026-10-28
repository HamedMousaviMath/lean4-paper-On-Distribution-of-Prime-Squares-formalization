import PrimeSquares.HighLowBalance

/-!
# Exact Orlicz growth estimates for the A_N endpoint

The paper uses Log x = 2 + |log x| and LogLog x = 2 + log (Log x).
All constants in the uniform bounds below are quantified before the density.
These results prove the logarithmic absorption used in Theorem 4.1; they do
not assume its endpoint estimate or any deep analytic theorem.
-/

open Filter Topology

namespace PrimeSquares

noncomputable def orliczWeight (κ L : ℝ) : ℝ := L ^ κ / (2 + Real.log L)

theorem orliczWeight_pos (κ : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    0 < orliczWeight κ L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)

theorem paperPhi_eq_exp_weight (c κ x : ℝ) :
    paperPhi c κ x = Real.exp (c * orliczWeight κ (paperLog x)) := by
  unfold paperPhi paperLogLog orliczWeight
  congr 1
  ring

theorem paperPhi_exp_neg (c κ t : ℝ) (ht : 0 ≤ t) :
    paperPhi c κ (Real.exp (-t)) = Real.exp (c * orliczWeight κ (2 + t)) := by
  rw [paperPhi_eq_exp_weight, paperLog_exp_neg t ht]

theorem log_div_orliczWeight_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L : ℝ => Real.log L / orliczWeight κ L) atTop (𝓝 0) := by
  have h1 := (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun L : ℝ => Real.log L ^ 2 / L ^ κ) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hκ).tendsto_div_nhds_zero
  have h := (h1.const_mul 2).add h2
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  have hp : L ^ κ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
  have hd : 2 + Real.log L ≠ 0 := by
    have := Real.log_nonneg (show 1 ≤ L by linarith)
    linarith
  dsimp [orliczWeight]
  field_simp

theorem inv_orliczWeight_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L : ℝ => (orliczWeight κ L)⁻¹) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_atTop hκ).const_div_atTop 2).add
    (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  dsimp [orliczWeight]
  field_simp

/-- A bounded additive error is negligible on the Orlicz exponent scale. -/
theorem bounded_div_orliczWeight_tendsto {κ M : ℝ} {e : ℝ → ℝ} (hκ : 0 < κ)
    (he : ∀ᶠ L : ℝ in atTop, |e L| ≤ M) :
    Tendsto (fun L => e L / orliczWeight κ L) atTop (𝓝 0) := by
  have hlo := (inv_orliczWeight_tendsto hκ).const_mul (-M)
  have hhi := (inv_orliczWeight_tendsto hκ).const_mul M
  simp only [mul_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with L heL hL
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (abs_le.mp heL).1 (orliczWeight_pos κ hL).le
  · filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with L heL hL
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (abs_le.mp heL).2 (orliczWeight_pos κ hL).le

theorem orliczWeight_div_self_tendsto {κ : ℝ} (hκ : κ < 1) :
    Tendsto (fun L : ℝ => orliczWeight κ L / L) atTop (𝓝 0) := by
  have hp : Tendsto (fun L : ℝ => L ^ (κ - 1)) atTop (𝓝 0) :=
    by simpa only [neg_sub] using tendsto_rpow_neg_atTop (show 0 < 1 - κ by linarith)
  have hi : Tendsto (fun L : ℝ => (2 + Real.log L)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left atTop 2 Real.tendsto_log_atTop).inv_tendsto_atTop
  have h := hp.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  rw [orliczWeight, Real.rpow_sub (show 0 < L by linarith), Real.rpow_one]
  ring

/-- Uniform logarithmic absorption, including the bounded range L>=2. -/
theorem rpow_le_exp_orliczWeight {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (m : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℝ, 2 ≤ L →
      L ^ m ≤ D * Real.exp (c * orliczWeight κ L) := by
  have hlim := (log_div_orliczWeight_tendsto hκ).const_mul |m|
  simp only [mul_zero] at hlim
  have he : ∀ᶠ L : ℝ in atTop,
      |m| * (Real.log L / orliczWeight κ L) < c :=
    hlim.eventually (eventually_lt_nhds hc)
  obtain ⟨T, hT⟩ := he.exists_forall_of_atTop
  let U : ℝ := max 2 T
  refine ⟨U ^ |m|, Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := by linarith
  have hU1 : 1 ≤ U := by dsimp [U]; have := le_max_left (2 : ℝ) T; linarith
  have hD : 1 ≤ U ^ |m| := Real.one_le_rpow hU1 (abs_nonneg _)
  by_cases hlarge : T ≤ L
  · have hw := orliczWeight_pos κ hL
    have hm : m * Real.log L ≤ c * orliczWeight κ L := by
      have hb : |m| * Real.log L < c * orliczWeight κ L := by
        apply (div_lt_iff₀ hw).mp
        simpa only [mul_div_assoc] using hT L hlarge
      have hl := Real.log_nonneg hL1
      nlinarith [mul_le_mul_of_nonneg_right (le_abs_self m) hl]
    calc
      L ^ m = Real.exp (m * Real.log L) := by
        rw [Real.rpow_def_of_pos (by linarith)]
        congr 1
        ring
      _ ≤ Real.exp (c * orliczWeight κ L) := Real.exp_le_exp.mpr hm
      _ ≤ U ^ |m| * Real.exp (c * orliczWeight κ L) :=
        le_mul_of_one_le_left (Real.exp_pos _).le hD
  · have hLU : L ≤ U := (le_of_not_ge hlarge).trans (le_max_right _ _)
    have hpow : L ^ m ≤ U ^ |m| :=
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self m)).trans
        (Real.rpow_le_rpow (by linarith) hLU (abs_nonneg _))
    exact hpow.trans (le_mul_of_one_le_right (Real.rpow_nonneg (zero_le_one.trans hU1) _) (by
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg hc.le (orliczWeight_pos κ hL).le))

theorem paperLog_rpow_le_paperPhi {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (m : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, (paperLog x) ^ m ≤ D * paperPhi c κ x := by
  obtain ⟨D, hD, hb⟩ := rpow_le_exp_orliczWeight hκ hc m
  refine ⟨D, hD, fun x => ?_⟩
  rw [paperPhi_eq_exp_weight]
  exact hb (paperLog x) (paperLog_two_le x)

/-- The Orlicz exponential has sublinear exponent, uniformly for L>=2. -/
theorem exp_orliczWeight_le_exp_linear {κ c ε : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℝ, 2 ≤ L →
      Real.exp (c * orliczWeight κ L) ≤ D * Real.exp (ε * L) := by
  have hlim := (orliczWeight_div_self_tendsto hκ1).const_mul c
  simp only [mul_zero] at hlim
  have he : ∀ᶠ L : ℝ in atTop, c * (orliczWeight κ L / L) < ε :=
    hlim.eventually (eventually_lt_nhds hε)
  obtain ⟨T, hT⟩ := he.exists_forall_of_atTop
  let U : ℝ := max 2 T
  refine ⟨Real.exp (c * U ^ κ), Real.exp_pos _, ?_⟩
  intro L hL
  have hL0 : 0 < L := by linarith
  have hU0 : 0 ≤ U := le_trans (by norm_num) (le_max_left _ _)
  have hD : 1 ≤ Real.exp (c * U ^ κ) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hc (Real.rpow_nonneg hU0 _))
  by_cases hlarge : T ≤ L
  · have hb : c * orliczWeight κ L ≤ ε * L := by
      apply (div_le_iff₀ hL0).mp
      simpa only [mul_div_assoc] using (hT L hlarge).le
    exact (Real.exp_le_exp.mpr hb).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le hD)
  · have hLU : L ≤ U := (le_of_not_ge hlarge).trans (le_max_right _ _)
    have hd : 1 ≤ 2 + Real.log L := by
      have := Real.log_nonneg (show 1 ≤ L by linarith)
      linarith
    have hw : orliczWeight κ L ≤ U ^ κ := by
      calc
        _ ≤ L ^ κ := div_le_self (Real.rpow_nonneg hL0.le _) hd
        _ ≤ U ^ κ := Real.rpow_le_rpow hL0.le hLU hκ0
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hc)).trans
      (le_mul_of_one_le_right (Real.exp_pos _).le
        (Real.one_le_exp_iff.mpr (mul_nonneg hε.le hL0.le)))

/-- Any fixed positive density power absorbs Phi. Both constants are fixed
before delta, and the entire interval 0<delta<=1 is included. -/
theorem paperPhi_le_inv_rpow {κ c ε : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      paperPhi c κ δ ≤ D * δ ^ (-ε) := by
  obtain ⟨D, hD, hb⟩ := exp_orliczWeight_le_exp_linear hκ0 hκ1 hc hε
  refine ⟨D * Real.exp (2 * ε), mul_pos hD (Real.exp_pos _), ?_⟩
  intro δ hδ hδ1
  rw [paperPhi_eq_exp_weight]
  calc
    _ ≤ D * Real.exp (ε * paperLog δ) := hb _ (paperLog_two_le δ)
    _ = (D * Real.exp (2 * ε)) * δ ^ (-ε) := by
      rw [paperLog_of_le_one hδ hδ1, Real.rpow_def_of_pos hδ,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem density_rpow_mul_paperPhi_le {κ c ε : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : 0 ≤ c) (hε : 0 < ε) (θ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      δ ^ θ * paperPhi c κ δ ≤ D * δ ^ (θ - ε) := by
  obtain ⟨D, hD, hb⟩ := paperPhi_le_inv_rpow hκ0 hκ1 hc hε
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδ1
  calc
    _ ≤ δ ^ θ * (D * δ ^ (-ε)) :=
      mul_le_mul_of_nonneg_left (hb δ hδ hδ1) (Real.rpow_nonneg hδ.le _)
    _ = D * δ ^ (θ - ε) := by rw [sub_eq_add_neg, Real.rpow_add hδ]; ring

end PrimeSquares
