import PrimeSquares.HighLowBalance

/-!
# Dyadic optimization with the source's upper cutoff

This proves the entire scalar implication behind `e:endimprovbn`, including
small preferred scales and an empty admissible range. The pairing estimate
and crude estimate are explicit hypotheses here; the next module proves them
for actual finite-set convolutions from the appropriate norm assumptions.
-/

namespace PrimeSquares

theorem highLowBalance_nearby {s r γ β δ J : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hJ : 2 ≤ J)
    (hJT : J ≤ highLowBalanceScale s r γ β δ)
    (hTJ : highLowBalanceScale s r γ β δ ≤ 2 * J) :
    δ * J ^ s * (Real.log J) ^ γ + δ ^ (1 / 2 : ℝ) * J ^ (-r) * (Real.log J) ^ β ≤
      ((highLowLogScale s r) ^ γ + (2 : ℝ) ^ r * (highLowLogScale s r) ^ β) *
        highLowEndpoint s r γ β δ := by
  have hγ : 0 ≤ γ := hβ.trans hβγ
  have hJpos : 0 < J := by linarith
  have hTpos := highLowBalanceScale_pos s r γ β hδ
  have hKpos : 0 < highLowLogScale s r :=
    lt_of_lt_of_le (by norm_num) (highLowLogScale_one_le hs hr)
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg (by linarith)
  have hlog : Real.log J ≤ highLowLogScale s r * paperLog δ :=
    (Real.log_le_log hJpos hJT).trans (log_highLowBalanceScale_le hs hr hβγ hδ hδ1)
  have hlg : (Real.log J) ^ γ ≤ (highLowLogScale s r) ^ γ * (paperLog δ) ^ γ := by
    simpa only [Real.mul_rpow hKpos.le (paperLog_pos δ).le] using
      Real.rpow_le_rpow hlogJ hlog hγ
  have hlb : (Real.log J) ^ β ≤ (highLowLogScale s r) ^ β * (paperLog δ) ^ β := by
    simpa only [Real.mul_rpow hKpos.le (paperLog_pos δ).le] using
      Real.rpow_le_rpow hlogJ hlog hβ
  have hJs : J ^ s ≤ (highLowBalanceScale s r γ β δ) ^ s :=
    Real.rpow_le_rpow hJpos.le hJT hs.le
  have hJr : J ^ (-r) ≤ (2 : ℝ) ^ r * (highLowBalanceScale s r γ β δ) ^ (-r) := by
    calc
      _ ≤ (highLowBalanceScale s r γ β δ / 2) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = _ := by
        rw [Real.div_rpow hTpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, inv_inv, mul_comm]
  have hlo : δ * J ^ s * (Real.log J) ^ γ ≤
      (highLowLogScale s r) ^ γ * highLowEndpoint s r γ β δ := by
    calc
      _ ≤ (δ * (highLowBalanceScale s r γ β δ) ^ s) *
          ((highLowLogScale s r) ^ γ * (paperLog δ) ^ γ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hJs hδ.le) hlg
          (Real.rpow_nonneg hlogJ _) (mul_nonneg hδ.le (Real.rpow_nonneg hTpos.le _))
      _ = (highLowLogScale s r) ^ γ *
          (δ * (highLowBalanceScale s r γ β δ) ^ s * (paperLog δ) ^ γ) := by ring
      _ = _ := by rw [highLowBalance_low_exact s r γ β hδ]
  have hhi : δ ^ (1 / 2 : ℝ) * J ^ (-r) * (Real.log J) ^ β ≤
      ((2 : ℝ) ^ r * (highLowLogScale s r) ^ β) * highLowEndpoint s r γ β δ := by
    calc
      _ ≤ (δ ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ r * (highLowBalanceScale s r γ β δ) ^ (-r))) *
          ((highLowLogScale s r) ^ β * (paperLog δ) ^ β) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hJr (Real.rpow_nonneg hδ.le _)) hlb
          (Real.rpow_nonneg hlogJ _) (by positivity)
      _ = ((2 : ℝ) ^ r * (highLowLogScale s r) ^ β) *
          (δ ^ (1 / 2 : ℝ) * (highLowBalanceScale s r γ β δ) ^ (-r) * (paperLog δ) ^ β) := by ring
      _ = _ := by rw [highLowBalance_high_exact (by linarith : s + r ≠ 0) γ β hδ]
  calc
    _ ≤ (highLowLogScale s r) ^ γ * highLowEndpoint s r γ β δ +
        ((2 : ℝ) ^ r * (highLowLogScale s r) ^ β) * highLowEndpoint s r γ β δ := add_le_add hlo hhi
    _ = _ := by ring

theorem highLowBalance_at_two {s r γ β δ : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : highLowBalanceScale s r γ β δ ≤ 2) :
    δ * (2 : ℝ) ^ s * (Real.log 2) ^ γ +
        δ ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-r) * (Real.log 2) ^ β ≤
      ((2 : ℝ) ^ s + 1) * highLowEndpoint s r γ β δ := by
  have hγ : 0 ≤ γ := hβ.trans hβγ
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlg : (Real.log (2 : ℝ)) ^ γ ≤ 1 := Real.rpow_le_one hlog hlog1 hγ
  have hlb : (Real.log (2 : ℝ)) ^ β ≤ (paperLog δ) ^ β :=
    Real.rpow_le_rpow hlog (hlog1.trans (by have := paperLog_two_le δ; linarith)) hβ
  have hpow : (2 : ℝ) ^ (-r) ≤ (highLowBalanceScale s r γ β δ) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (highLowBalanceScale_pos s r γ β hδ) hT (by linarith)
  have hlo : δ * (2 : ℝ) ^ s * (Real.log 2) ^ γ ≤
      (2 : ℝ) ^ s * highLowEndpoint s r γ β δ := by
    calc
      _ ≤ δ * (2 : ℝ) ^ s := by
        have h : δ * (2 : ℝ) ^ s * (Real.log 2) ^ γ ≤ δ * (2 : ℝ) ^ s * 1 :=
          mul_le_mul_of_nonneg_left hlg
          (mul_nonneg hδ.le (Real.rpow_nonneg (by norm_num) _))
        simpa only [mul_one] using h
      _ ≤ _ := by
        rw [mul_comm δ]
        exact mul_le_mul_of_nonneg_left (density_le_highLowEndpoint hs hr hγ hβ hδ hδ1)
          (Real.rpow_nonneg (by norm_num) _)
  have hhi : δ ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-r) * (Real.log 2) ^ β ≤
      highLowEndpoint s r γ β δ := by
    calc
      _ ≤ (δ ^ (1 / 2 : ℝ) * (highLowBalanceScale s r γ β δ) ^ (-r)) * (paperLog δ) ^ β :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hδ.le _)) hlb
          (Real.rpow_nonneg hlog _) (by
            exact mul_nonneg (Real.rpow_nonneg hδ.le _)
              (Real.rpow_nonneg (highLowBalanceScale_pos s r γ β hδ).le _))
      _ = _ := highLowBalance_high_exact (by linarith : s + r ≠ 0) γ β hδ
  calc
    _ ≤ (2 : ℝ) ^ s * highLowEndpoint s r γ β δ + highLowEndpoint s r γ β δ := add_le_add hlo hhi
    _ = _ := by ring

/-- Raising the exceeded cutoff to s cancels exactly the division by s. -/
theorem highLow_power_above_cutoff {N s v T : ℝ} (hN : 0 < N) (hs : 0 < s) (hT : 0 < T)
    (hcut : N ^ ((1 - v) / s) / 10 < T) : N ^ (1 - v) ≤ (10 : ℝ) ^ s * T ^ s := by
  have he := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _)
    (show N ^ ((1 - v) / s) ≤ 10 * T by linarith) hs.le
  rw [← Real.rpow_mul hN.le, div_mul_cancel₀ (1 - v) hs.ne',
    Real.mul_rpow (by norm_num) hT.le] at he
  exact he

noncomputable def highLowOptimizationConstant (s r γ β : ℝ) : ℝ :=
  ((highLowLogScale s r) ^ γ + (2 : ℝ) ^ r * (highLowLogScale s r) ^ β) +
    (10 : ℝ) ^ s + ((2 : ℝ) ^ s + 1) + (20 : ℝ) ^ s

theorem highLowOptimizationConstant_pos {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (γ β : ℝ) :
    0 < highLowOptimizationConstant s r γ β := by
  have hK : 0 < highLowLogScale s r :=
    lt_of_lt_of_le (by norm_num) (highLowLogScale_one_le hs hr)
  dsimp only [highLowOptimizationConstant]
  positivity

/-- Uniform scalar endpoint, using only admissible dyadic decomposition bounds.
The cutoff may be below two; that case is proved from the crude estimate. -/
theorem highLow_scalar_endpoint {s r γ β N v δ R C : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hcrude : R ≤ C * δ * N ^ (1 - v))
    (hdecomp : ∀ k : ℕ, 2 ≤ (2 : ℝ) ^ k → (2 : ℝ) ^ k ≤ N ^ ((1 - v) / s) / 10 →
      R ≤ C * (δ * ((2 : ℝ) ^ k) ^ s * (Real.log ((2 : ℝ) ^ k)) ^ γ +
        δ ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ k) ^ (-r) * (Real.log ((2 : ℝ) ^ k)) ^ β)) :
    R ≤ C * highLowOptimizationConstant s r γ β * highLowEndpoint s r γ β δ := by
  let K₁ := (highLowLogScale s r) ^ γ + (2 : ℝ) ^ r * (highLowLogScale s r) ^ β
  have hKlog : 0 < highLowLogScale s r :=
    lt_of_lt_of_le (by norm_num) (highLowLogScale_one_le hs hr)
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  have h10 : (0 : ℝ) ≤ 10 ^ s := by positivity
  have h2 : (0 : ℝ) ≤ 2 ^ s + 1 := by positivity
  have h20 : (0 : ℝ) ≤ 20 ^ s := by positivity
  have hE : 0 ≤ highLowEndpoint s r γ β δ := (highLowEndpoint_pos s r γ β hδ).le
  have enlarge (K : ℝ) (hK : K ≤ highLowOptimizationConstant s r γ β)
      (h : R ≤ C * K * highLowEndpoint s r γ β δ) :
      R ≤ C * highLowOptimizationConstant s r γ β * highLowEndpoint s r γ β δ :=
    h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC) hE)
  by_cases hT : 2 ≤ highLowBalanceScale s r γ β δ
  · by_cases hcut : highLowBalanceScale s r γ β δ ≤ N ^ ((1 - v) / s) / 10
    · obtain ⟨k, hk2, hkT, hTk⟩ := exists_dyadic_below hT
      apply enlarge K₁
      · dsimp only [highLowOptimizationConstant]
        change K₁ ≤ K₁ + _ + _ + _
        linarith
      · calc
          _ ≤ C * (δ * ((2 : ℝ) ^ k) ^ s * (Real.log ((2 : ℝ) ^ k)) ^ γ +
              δ ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ k) ^ (-r) * (Real.log ((2 : ℝ) ^ k)) ^ β) :=
            hdecomp k hk2 (hkT.trans hcut)
          _ ≤ C * (K₁ * highLowEndpoint s r γ β δ) :=
            mul_le_mul_of_nonneg_left (highLowBalance_nearby hs hr hβ hβγ hδ hδ1 hk2 hkT hTk.le) hC
          _ = _ := by ring
    · apply enlarge ((10 : ℝ) ^ s)
      · dsimp only [highLowOptimizationConstant]
        change (10 : ℝ) ^ s ≤ K₁ + _ + _ + _
        linarith
      · calc
          _ ≤ C * δ * N ^ (1 - v) := hcrude
          _ ≤ C * δ * ((10 : ℝ) ^ s * (highLowBalanceScale s r γ β δ) ^ s) :=
            mul_le_mul_of_nonneg_left (highLow_power_above_cutoff hN hs
              (highLowBalanceScale_pos s r γ β hδ) (lt_of_not_ge hcut)) (mul_nonneg hC hδ.le)
          _ = C * (10 : ℝ) ^ s * (δ * (highLowBalanceScale s r γ β δ) ^ s) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (highLowBalance_low_le_endpoint (hβ.trans hβγ) hδ)
            (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
  · by_cases hcut : 2 ≤ N ^ ((1 - v) / s) / 10
    · apply enlarge ((2 : ℝ) ^ s + 1)
      · dsimp only [highLowOptimizationConstant]
        change (2 : ℝ) ^ s + 1 ≤ K₁ + _ + _ + _
        linarith
      · have h := hdecomp 1 (by norm_num) (by simpa only [pow_one] using hcut)
        simp only [pow_one] at h
        calc
          _ ≤ C * (δ * (2 : ℝ) ^ s * (Real.log 2) ^ γ +
              δ ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-r) * (Real.log 2) ^ β) := h
          _ ≤ C * (((2 : ℝ) ^ s + 1) * highLowEndpoint s r γ β δ) :=
            mul_le_mul_of_nonneg_left (highLowBalance_at_two hs hr hβ hβγ hδ hδ1 (le_of_not_ge hT)) hC
          _ = _ := by ring
    · apply enlarge ((20 : ℝ) ^ s)
      · dsimp only [highLowOptimizationConstant]
        change (20 : ℝ) ^ s ≤ K₁ + _ + _ + _
        linarith
      · have hp : N ^ (1 - v) ≤ (20 : ℝ) ^ s := by
          simpa only [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) (by norm_num : (0 : ℝ) ≤ 2),
            show (10 : ℝ) * 2 = 20 by norm_num] using
            highLow_power_above_cutoff hN hs (by norm_num : (0 : ℝ) < 2) (lt_of_not_ge hcut)
        calc
          _ ≤ C * δ * N ^ (1 - v) := hcrude
          _ ≤ C * δ * (20 : ℝ) ^ s := mul_le_mul_of_nonneg_left hp (mul_nonneg hC hδ.le)
          _ = C * (20 : ℝ) ^ s * δ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (density_le_highLowEndpoint hs hr (hβ.trans hβγ) hβ hδ hδ1) (mul_nonneg hC h20)

end PrimeSquares
