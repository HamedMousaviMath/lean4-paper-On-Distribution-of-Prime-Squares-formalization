import PrimeSquares.HighLowTheorem

/-!
# Exponents and removal of the restricted endpoint losses

Source: Corollary 4.15, the deduction of e:restrictedimproving.
All constants in the loss estimates are uniform over 0<delta<=1. The
strong interpolation step is not asserted here.
-/

namespace PrimeSquares

noncomputable def improvingCriticalExponent (s r : ℝ) : ℝ := 2 * (s + r) / (2 * r + s)

noncomputable def holderConjugate (p : ℝ) : ℝ := p / (p - 1)

theorem holderConjugate_two : holderConjugate 2 = 2 := by norm_num [holderConjugate]

theorem improvingCriticalExponent_one_lt {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    1 < improvingCriticalExponent s r := by
  unfold improvingCriticalExponent
  apply (one_lt_div (by linarith : 0 < 2 * r + s)).mpr
  linarith

theorem improvingCriticalExponent_lt_two {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    improvingCriticalExponent s r < 2 := by
  unfold improvingCriticalExponent
  apply (div_lt_iff₀ (by linarith : 0 < 2 * r + s)).mpr
  linarith

theorem improvingCriticalExponent_inv {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    1 / improvingCriticalExponent s r = highLowDensityExponent s r := by
  unfold improvingCriticalExponent highLowDensityExponent
  field_simp
  ring

theorem improving_reciprocal_gap {s r p : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hp : improvingCriticalExponent s r < p) :
    0 < highLowDensityExponent s r - 1 / p := by
  have hp₀ : 0 < improvingCriticalExponent s r :=
    zero_lt_one.trans (improvingCriticalExponent_one_lt hs hr)
  have h := one_div_lt_one_div_of_lt hp₀ hp
  rw [improvingCriticalExponent_inv hs hr] at h
  linarith

theorem holderConjugate_pos {p : ℝ} (hp : 1 < p) : 0 < holderConjugate p :=
  div_pos (by linarith) (by linarith)

theorem holderConjugate_one_lt {p : ℝ} (hp : 1 < p) : 1 < holderConjugate p := by
  unfold holderConjugate
  exact (one_lt_div (by linarith : 0 < p - 1)).mpr (by linarith)

theorem holderConjugate_reciprocal {p : ℝ} (hp : 1 < p) :
    1 / holderConjugate p = 1 - 1 / p := by
  unfold holderConjugate
  field_simp

theorem holderConjugate_scaling {p : ℝ} (hp : 1 < p) :
    1 / holderConjugate p - 1 / p = 1 - 2 / p := by
  rw [holderConjugate_reciprocal hp]
  ring

theorem improving_reciprocal_half {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (1 / 2 : ℝ) ≤ 1 / p := by
  exact one_div_le_one_div_of_le hp hp2

theorem density_power_scaling (N f g p : ℝ) (hN : 0 < N) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    N * (f * g / N ^ 2) ^ (1 / p) = N ^ (1 - 2 / p) * f ^ (1 / p) * g ^ (1 / p) := by
  rw [Real.div_rpow (mul_nonneg hf hg) (sq_nonneg N), Real.mul_rpow hf hg,
    ← Real.rpow_natCast_mul hN.le]
  rw [Real.rpow_sub hN, Real.rpow_one]
  norm_num only [Nat.cast_ofNat]
  have he : (2 : ℝ) * (1 / p) = 2 / p := by ring
  rw [he]
  ring

theorem finiteSetDensity_power_scaling {N p : ℝ} (hN : 0 < N) (F G : Finset ℤ) :
    N * (finiteSetDensity N F G) ^ (1 / p) =
      N ^ (1 - 2 / p) * (F.card : ℝ) ^ (1 / p) * (G.card : ℝ) ^ (1 / p) :=
  density_power_scaling N (F.card : ℝ) (G.card : ℝ) p hN (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A fixed logarithmic power costs any prescribed positive density power. -/
theorem paperLog_rpow_le_inv_density {ε : ℝ} (hε : 0 < ε) (m : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (paperLog δ) ^ m ≤ D * δ ^ (-ε) := by
  obtain ⟨DL, hDL, hL⟩ := paperLog_rpow_le_paperPhi
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1) m
  obtain ⟨DP, hDP, hP⟩ := paperPhi_le_inv_rpow
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1) hε
  refine ⟨DL * DP, mul_pos hDL hDP, ?_⟩
  intro δ hδ hδ1
  exact (hL δ).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hP δ hδ hδ1) hDL.le)

theorem density_power_log_loss {θ σ : ℝ} (hgap : σ < θ) (m : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      δ ^ θ * (paperLog δ) ^ m ≤ D * δ ^ σ := by
  obtain ⟨D, hD, hb⟩ := paperLog_rpow_le_inv_density (sub_pos.mpr hgap) m
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδ1
  calc
    _ ≤ δ ^ θ * (D * δ ^ (-(θ - σ))) :=
      mul_le_mul_of_nonneg_left (hb δ hδ hδ1) (Real.rpow_nonneg hδ.le _)
    _ = D * δ ^ σ := by
      have he : θ + -(θ - σ) = σ := by ring
      calc
        _ = D * (δ ^ θ * δ ^ (-(θ - σ))) := by ring
        _ = _ := by rw [← Real.rpow_add hδ, he]

theorem density_power_phi_loss {κ c θ σ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : 0 ≤ c) (hgap : σ < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      δ ^ θ * paperPhi c κ δ ≤ D * δ ^ σ := by
  obtain ⟨D, hD, hb⟩ := density_rpow_mul_paperPhi_le hκ0 hκ1 hc (sub_pos.mpr hgap) θ
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδ1
  have he : θ - (θ - σ) = σ := by ring
  simpa only [he] using hb δ hδ hδ1

theorem density_power_log_loss_nonneg {θ σ : ℝ} (hσ : 0 < σ) (hgap : σ < θ) (m : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      δ ^ θ * (paperLog δ) ^ m ≤ D * δ ^ σ := by
  obtain ⟨D, hD, hb⟩ := density_power_log_loss hgap m
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδ1
  by_cases hz : δ = 0
  · subst δ
    simp only [Real.zero_rpow (ne_of_gt (hσ.trans hgap)), Real.zero_rpow hσ.ne',
      zero_mul, mul_zero, le_refl]
  · exact hb δ (lt_of_le_of_ne hδ (Ne.symm hz)) hδ1

theorem density_power_phi_loss_nonneg {κ c θ σ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : 0 ≤ c) (hσ : 0 < σ) (hgap : σ < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      δ ^ θ * paperPhi c κ δ ≤ D * δ ^ σ := by
  obtain ⟨D, hD, hb⟩ := density_power_phi_loss hκ0 hκ1 hc hgap
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδ1
  by_cases hz : δ = 0
  · subst δ
    simp only [Real.zero_rpow (ne_of_gt (hσ.trans hgap)), Real.zero_rpow hσ.ne',
      zero_mul, mul_zero, le_refl]
  · exact hb δ (lt_of_le_of_ne hδ (Ne.symm hz)) hδ1

end PrimeSquares
