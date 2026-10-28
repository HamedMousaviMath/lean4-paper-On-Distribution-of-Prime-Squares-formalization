import PrimeSquares.OrliczPairing

/-!
# Uniform scalar A_N endpoint, including bounded densities and empty ranges

The positive-kernel and genuine operator pairing bridges are in separate
modules. This module proves the entire scalar implication; it does not take
an optimization or asymptotic conclusion as a hypothesis.
-/

open Filter Topology

namespace PrimeSquares

theorem orliczLeadingCoefficient_pos {s r c₁ : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hc₁ : 0 < c₁) (κ : ℝ) : 0 < orliczLeadingCoefficient s r c₁ κ := by
  exact div_pos (mul_pos hc₁ hs) (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by linarith) _))

theorem exp_two_sub_paperLog {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp (2 - paperLog δ) = δ := by
  rw [paperLog_of_le_one hδ hδ1]
  have he : (2 : ℝ) - (2 - Real.log δ) = Real.log δ := by ring
  rw [he, Real.exp_log hδ]

theorem bounded_density_power_bounds {δ θ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : θ ≤ 1) (hT : paperLog δ ≤ T) :
    δ ≤ δ ^ θ ∧ δ ^ (1 / 2 : ℝ) ≤ Real.exp T * δ ^ θ := by
  have hd : δ ≤ δ ^ θ := by
    calc
      _ = δ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hθ
  have hsqrt : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hlog : 0 ≤ T + Real.log δ := by
    rw [paperLog_of_le_one hδ hδ1] at hT
    linarith
  have he : 1 ≤ Real.exp T * δ := by
    conv_rhs => rw [← Real.exp_log hδ]
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr hlog
  exact ⟨hd, hsqrt.trans (he.trans (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le))⟩

noncomputable def orliczCompactConstant (s r α c₁ κ M T : ℝ) : ℝ :=
  (4 : ℝ) ^ s * (Real.log 4) ^ α + Real.exp T *
    ((4 : ℝ) ^ (-r) * orliczHighFactor c₁ κ 4 + (4 : ℝ) ^ (-r) * (Real.log 4) ^ M)

theorem orliczCompactConstant_pos (s r α c₁ κ M T : ℝ) :
    0 < orliczCompactConstant s r α c₁ κ M T := by
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold orliczCompactConstant orliczHighFactor
  positivity

theorem orliczScalarSum_compact {N δ θ T A : ℝ} (hN : 1 ≤ N) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hθ : θ ≤ 1) (hT : paperLog δ ≤ T) (hA : 0 ≤ A)
    (s r α c₁ κ M : ℝ) :
    orliczScalarSum s r α c₁ κ M A N δ 4 ≤
      orliczCompactConstant s r α c₁ κ M T * δ ^ θ := by
  obtain ⟨hd, hroot⟩ := bounded_density_power_bounds hδ hδ1 hθ hT
  have hl : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  have hLo : 0 ≤ (4 : ℝ) ^ s * (Real.log 4) ^ α := by positivity
  have hHi : 0 ≤ (4 : ℝ) ^ (-r) * orliczHighFactor c₁ κ 4 := by
    unfold orliczHighFactor
    positivity
  have hErr : 0 ≤ (4 : ℝ) ^ (-r) * (Real.log 4) ^ M := by positivity
  have h1 := mul_le_mul_of_nonneg_right hd hLo
  have h2 := mul_le_mul_of_nonneg_right hroot hHi
  have h3 := mul_le_mul_of_nonneg_right hroot hErr
  have he := mul_le_mul_of_nonneg_left (error_decay_factor_le_one hN hA)
    (mul_nonneg (Real.rpow_nonneg hδ.le (1 / 2 : ℝ)) hErr)
  simp only [mul_one] at he
  unfold orliczScalarSum orliczCompactConstant
  nlinarith only [h1, h2, h3, he]

/-- Choosing the complementary-range constant small enough also makes Q=4
admissible in the remaining bounded-density range. -/
theorem orlicz_small_cutoff {c₀ k : ℝ} (hc₀ : 0 < c₀) (hk : 0 < k) :
    let d := c₀ / (k + 1 + Real.log 4)
    0 < d ∧ d ≤ c₀ / (k + 1) ∧
      ∀ L t : ℝ, 2 ≤ L → L ≤ d * t → Real.log 4 ≤ c₀ * t := by
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hk1 : 0 < k + 1 := by linarith
  have hden : 0 < k + 1 + Real.log 4 := by linarith
  dsimp only
  refine ⟨div_pos hc₀ hden, div_le_div_of_nonneg_left hc₀.le hk1 (by linarith), ?_⟩
  intro L t hL hcut
  have hmul := mul_le_mul_of_nonneg_left hcut hden.le
  have he : (k + 1 + Real.log 4) * (c₀ / (k + 1 + Real.log 4) * t) = c₀ * t := by
    field_simp
  rw [he] at hmul
  nlinarith

/-- Complete uniform scalar implication for A_N. CB and CA are fixed norm
constants. Both cutoffs and the bounded-density range are proved here. -/
theorem orlicz_scalar_endpoint {s r c₁ κ cstar a c c₀ CB CA : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hc₁ : 0 < c₁) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hstar : orliczLeadingCoefficient s r c₁ κ < cstar)
    (ha : 0 ≤ a) (hc : 0 < c) (hc₀ : 0 < c₀) (hCB : 0 < CB) (hCA : 0 < CA)
    (α M τ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ N δ RA RB : ℝ, 1 ≤ N → 0 < δ → δ ≤ 1 →
      RA ≤ (Real.log N) ^ a * RB →
      RB ≤ CB * δ ^ highLowDensityExponent s r * (paperLog δ) ^ τ →
      (∀ j : ℕ, 2 ≤ (2 : ℝ) ^ j → Real.log ((2 : ℝ) ^ j) ≤ c₀ * (Real.log N) ^ c →
        RA ≤ CA * orliczScalarSum s r α c₁ κ M 1 N δ ((2 : ℝ) ^ j)) →
      RA ≤ D * δ ^ highLowDensityExponent s r * paperPhi cstar κ δ := by
  have hstar0 : 0 < cstar := (orliczLeadingCoefficient_pos hs hr hc₁ κ).trans hstar
  let k : ℝ := 1 / (2 * (s + r))
  have hk : 0 < k := div_pos zero_lt_one (by linarith)
  let d : ℝ := c₀ / (k + 1 + Real.log 4)
  obtain ⟨hd, hdle, hfour⟩ := orlicz_small_cutoff hc₀ hk
  obtain ⟨DC, hDC, hcomp⟩ := log_density_domination_le_orlicz hκ0 hstar0 ha hc hd
    (highLowDensityExponent s r) τ
  obtain ⟨n, hn, hraw⟩ := exists_admissible_dyadic_orlicz_bound hs hr hc₁ hκ0 hκ1 hstar c₀ c
  obtain ⟨T, hT⟩ := (hraw α M).exists_forall_of_atTop
  let CC := orliczCompactConstant s r α c₁ κ M T
  have hCC : 0 < CC := orliczCompactConstant_pos s r α c₁ κ M T
  let D := CB * DC + 3 * CA + CA * CC
  have hD : 0 < D := by dsimp [D]; nlinarith [mul_pos hCB hDC, mul_pos hCA hCC]
  refine ⟨D, hD, ?_⟩
  intro N δ RA RB hN hδ hδ1 hdom hB hdec
  have hδpow : 0 ≤ δ ^ highLowDensityExponent s r := Real.rpow_nonneg hδ.le _
  have hΦ : 1 ≤ paperPhi cstar κ δ := paperPhi_one_le hstar0.le κ δ
  have hE : 0 ≤ δ ^ highLowDensityExponent s r * paperPhi cstar κ δ :=
    mul_nonneg hδpow (paperPhi_pos _ _ _).le
  by_cases hcut : d * (Real.log N) ^ c ≤ paperLog δ
  · have hc1 := hcomp N δ hN hδ hδ1 hcut
    have hbn := mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (Real.log_nonneg hN) a)
    have hra : RA ≤ CB * DC * (δ ^ highLowDensityExponent s r * paperPhi cstar κ δ) := by
      calc
        _ ≤ (Real.log N) ^ a * (CB * δ ^ highLowDensityExponent s r * (paperLog δ) ^ τ) :=
          hdom.trans hbn
        _ = CB * ((Real.log N) ^ a * δ ^ highLowDensityExponent s r * (paperLog δ) ^ τ) := by ring
        _ ≤ CB * (DC * δ ^ highLowDensityExponent s r * paperPhi cstar κ δ) :=
          mul_le_mul_of_nonneg_left hc1 hCB.le
        _ = _ := by ring
    have hcoef : CB * DC ≤ D := by dsimp [D]; nlinarith [mul_pos hCB hDC, mul_pos hCA hCC]
    simpa only [mul_assoc] using hra.trans (mul_le_mul_of_nonneg_right hcoef hE)
  · have hsmall : paperLog δ ≤ d * (Real.log N) ^ c := (lt_of_not_ge hcut).le
    by_cases hlarge : T ≤ paperLog δ
    · have hdc : paperLog δ ≤ c₀ / (k + 1) * (Real.log N) ^ c :=
        hsmall.trans (mul_le_mul_of_nonneg_right hdle (Real.rpow_nonneg (Real.log_nonneg hN) _))
      have hraw' := hT (paperLog δ) hlarge N 1 hN (by norm_num) hdc
      dsimp only at hraw'
      rw [exp_two_sub_paperLog hδ hδ1] at hraw'
      have hra := (hdec (n (paperLog δ)) (hn _) hraw'.1).trans
        (mul_le_mul_of_nonneg_left hraw'.2 hCA.le)
      have hcoef : 3 * CA ≤ D := by dsimp [D]; nlinarith [mul_pos hCB hDC, mul_pos hCA hCC]
      change RA ≤ CA * _ at hra
      have hra' : RA ≤ 3 * CA * (δ ^ highLowDensityExponent s r * paperPhi cstar κ δ) := by
        simpa only [orliczScalarSum, orliczHighFactor, mul_assoc, mul_comm, mul_left_comm] using hra
      simpa only [mul_assoc] using hra'.trans (mul_le_mul_of_nonneg_right hcoef hE)
    · have hfour' := hfour (paperLog δ) ((Real.log N) ^ c) (paperLog_two_le δ) hsmall
      have hdec4 : RA ≤ CA * orliczScalarSum s r α c₁ κ M 1 N δ 4 := by
        simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
          hdec 2 (by norm_num) (by simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using hfour')
      have hcompact := orliczScalarSum_compact hN hδ hδ1
        (highLowDensityExponent_le_one hs.le hr) (le_of_not_ge hlarge) (by norm_num : (0 : ℝ) ≤ 1)
        s r α c₁ κ M
      have hra : RA ≤ CA * CC * (δ ^ highLowDensityExponent s r * paperPhi cstar κ δ) := by
        calc
          _ ≤ CA * (CC * δ ^ highLowDensityExponent s r) :=
            hdec4.trans (mul_le_mul_of_nonneg_left hcompact hCA.le)
          _ ≤ CA * (CC * (δ ^ highLowDensityExponent s r * paperPhi cstar κ δ)) := by
            apply mul_le_mul_of_nonneg_left _ hCA.le
            apply mul_le_mul_of_nonneg_left _ hCC.le
            exact le_mul_of_one_le_right hδpow hΦ
          _ = _ := by ring
      have hcoef : CA * CC ≤ D := by dsimp [D]; nlinarith [mul_pos hCB hDC, mul_pos hCA hCC]
      simpa only [mul_assoc] using hra.trans (mul_le_mul_of_nonneg_right hcoef hE)

end PrimeSquares
