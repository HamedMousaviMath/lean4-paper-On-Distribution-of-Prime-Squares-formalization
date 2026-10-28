import PrimeSquares.OrliczBalance

/-!
# Actual scalar A_N contributions at the sharp dyadic balance

The conclusion bounds the sum of low, high and polynomial error terms.
The N-dependent cutoff, the bounded-density range and the operator pairing
bridge are not assumed to have been proved by this module.
-/

open Filter Topology

namespace PrimeSquares

theorem paperLog_exp_two_sub {L : ℝ} (hL : 2 ≤ L) :
    paperLog (Real.exp (2 - L)) = L := by
  have hδ1 : Real.exp (2 - L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [paperLog_of_le_one (Real.exp_pos _) hδ1, Real.log_exp]
  ring

theorem orlicz_low_term_exact (s k L α Q : ℝ) (hQ : 1 < Q) :
    Real.exp (2 - L) * Q ^ s * (Real.log Q) ^ α =
      (Real.exp (2 - L)) ^ (1 - s * k) *
        Real.exp (s * (Real.log Q - k * L) + α * Real.log (Real.log Q) + 2 * s * k) := by
  have hQ0 : 0 < Q := by linarith
  rw [Real.rpow_def_of_pos hQ0, Real.rpow_def_of_pos (Real.log_pos hQ),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  simp only [← Real.exp_add]
  congr 1
  ring

theorem orlicz_high_term_exact (s r k L H Q : ℝ) (hQ : 0 < Q)
    (hbalance : (s + r) * k = 1 / 2) :
    (Real.exp (2 - L)) ^ (1 / 2 : ℝ) * Q ^ (-r) * Real.exp H =
      (Real.exp (2 - L)) ^ (1 - s * k) *
        Real.exp (-r * (Real.log Q - k * L) + H - 2 * r * k) := by
  have hθ : 1 - s * k = 1 / 2 + r * k := by nlinarith
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hQ,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  simp only [← Real.exp_add]
  congr 1
  rw [hθ]
  ring

/-- A genuine dyadic Q controls the actual three scalar terms with every
coefficient above the printed sharp leading coefficient. The fixed error
power M is arbitrary. The factor (1+log N)^(-A), when <=1, only improves
the third term; it has not been used here. -/
theorem exists_dyadic_orlicz_scalar_bound {s r c₁ κ cstar : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hc₁ : 0 < c₁) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hstar : orliczLeadingCoefficient s r c₁ κ < cstar) :
    ∃ b : ℝ, 0 < b ∧ ∃ n : ℝ → ℕ,
      (∀ L : ℝ, 2 ≤ (2 : ℝ) ^ n L) ∧
      (∀ᶠ L : ℝ in atTop, (2 : ℝ) ^ n L ≤
        Real.exp (orliczLogScale (1 / (2 * (s + r))) b κ L)) ∧
      ∀ α M : ℝ, ∀ᶠ L : ℝ in atTop,
        let δ := Real.exp (2 - L)
        let Q := (2 : ℝ) ^ n L
        δ * Q ^ s * (Real.log Q) ^ α +
          δ ^ (1 / 2 : ℝ) * Q ^ (-r) *
            Real.exp (c₁ * (Real.log Q) ^ κ / Real.log (Real.log Q)) +
          δ ^ (1 / 2 : ℝ) * Q ^ (-r) * (Real.log Q) ^ M ≤
            3 * δ ^ highLowDensityExponent s r * paperPhi cstar κ δ := by
  obtain ⟨b, hb, n, hn, hnup, hbal⟩ := exists_dyadic_orlicz_balance hs hr hc₁ hκ0 hκ1 hstar
  refine ⟨b, hb, n, hn, hnup, ?_⟩
  intro α M
  filter_upwards [hbal α M, eventually_ge_atTop (2 : ℝ)] with L hbal hL
  let Q : ℝ := (2 : ℝ) ^ n L
  let k : ℝ := 1 / (2 * (s + r))
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num) (hn L)
  have hQ0 : 0 < Q := by linarith
  have hbalance : (s + r) * k = 1 / 2 := by dsimp [k]; field_simp
  have hθ : highLowDensityExponent s r = 1 - s * k := by
    dsimp [highLowDensityExponent, k]
    ring
  have hΦ : paperPhi cstar κ (Real.exp (2 - L)) = Real.exp (cstar * orliczWeight κ L) := by
    rw [paperPhi_eq_exp_weight, paperLog_exp_two_sub hL]
  let E : ℝ := (Real.exp (2 - L)) ^ (1 - s * k) * Real.exp (cstar * orliczWeight κ L)
  have hE : 0 ≤ (Real.exp (2 - L)) ^ (1 - s * k) := Real.rpow_nonneg (Real.exp_pos _).le _
  have hlo : Real.exp (2 - L) * Q ^ s * (Real.log Q) ^ α ≤ E := by
    rw [orlicz_low_term_exact s k L α Q hQ]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbal.1) hE
  have hhi : (Real.exp (2 - L)) ^ (1 / 2 : ℝ) * Q ^ (-r) *
      Real.exp (c₁ * (Real.log Q) ^ κ / Real.log (Real.log Q)) ≤ E := by
    rw [orlicz_high_term_exact s r k L _ Q hQ0 hbalance]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbal.2.1) hE
  have herr : (Real.exp (2 - L)) ^ (1 / 2 : ℝ) * Q ^ (-r) * (Real.log Q) ^ M ≤ E := by
    rw [Real.rpow_def_of_pos (Real.log_pos hQ)]
    rw [orlicz_high_term_exact s r k L _ Q hQ0 hbalance]
    apply mul_le_mul_of_nonneg_left _ hE
    apply Real.exp_le_exp.mpr
    convert hbal.2.2 using 1
    ring
  dsimp only
  rw [hθ, hΦ]
  dsimp only [E, Q] at hlo hhi herr
  linarith

end PrimeSquares
