import PrimeSquares.HighLowNotation

/-!
# Exact scalar balancing for the B_N estimate in Theorem 4.1

The normalizations and logarithmic exponents are those of `e:Jchoice` and
`e:endimprovbn`. These lemmas check the actual real-power algebra, not an
assumed optimization theorem. Truncation and finite-set pairings are handled
in subsequent modules.
-/

namespace PrimeSquares

noncomputable def highLowDensityExponent (s r : ℝ) : ℝ := 1 - s / (2 * (s + r))

noncomputable def highLowLogExponent (s r γ β : ℝ) : ℝ := γ + s * (β - γ) / (s + r)

noncomputable def highLowBalanceScale (s r γ β δ : ℝ) : ℝ :=
  δ ^ (-(1 / (2 * (s + r)))) * (paperLog δ) ^ ((β - γ) / (s + r))

noncomputable def highLowEndpoint (s r γ β δ : ℝ) : ℝ :=
  δ ^ highLowDensityExponent s r * (paperLog δ) ^ highLowLogExponent s r γ β

theorem highLowDensityExponent_pos {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    0 < highLowDensityExponent s r := by
  have hsr : 0 < 2 * (s + r) := by linarith
  dsimp only [highLowDensityExponent]
  have hd : s / (2 * (s + r)) < 1 := (div_lt_one hsr).mpr (by linarith)
  linarith

theorem highLowDensityExponent_le_one {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    highLowDensityExponent s r ≤ 1 := by
  dsimp only [highLowDensityExponent]
  have := div_nonneg hs (show 0 ≤ 2 * (s + r) by linarith)
  linarith

theorem highLowLogExponent_nonneg {s r γ β : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hγ : 0 ≤ γ) (hβ : 0 ≤ β) :
    0 ≤ highLowLogExponent s r γ β := by
  have he : highLowLogExponent s r γ β = (r * γ + s * β) / (s + r) := by
    dsimp only [highLowLogExponent]
    field_simp
    ring
  rw [he]
  exact div_nonneg (add_nonneg (mul_nonneg hr.le hγ) (mul_nonneg hs.le hβ)) (by linarith)

theorem highLowBalanceScale_pos (s r γ β : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < highLowBalanceScale s r γ β δ := by
  exact mul_pos (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos (paperLog_pos δ) _)

theorem highLowEndpoint_pos (s r γ β : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < highLowEndpoint s r γ β δ := by
  exact mul_pos (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos (paperLog_pos δ) _)

theorem highLowEndpoint_zero {s r γ β : ℝ} (hs : 0 < s) (hr : 0 < r) :
    highLowEndpoint s r γ β 0 = 0 := by
  simp only [highLowEndpoint, Real.zero_rpow (ne_of_gt (highLowDensityExponent_pos hs hr)), zero_mul]

theorem rpow_product_balance (d L a b c e f : ℝ) (hd : 0 < d) (hL : 0 < L) :
    d ^ a * (d ^ b * L ^ c) ^ e * L ^ f = d ^ (a + b * e) * L ^ (c * e + f) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hL.le _),
    ← Real.rpow_mul hd.le, ← Real.rpow_mul hL.le]
  calc
    _ = (d ^ a * d ^ (b * e)) * (L ^ (c * e) * L ^ f) := by ring
    _ = _ := by rw [← Real.rpow_add hd, ← Real.rpow_add hL]

/-- The low contribution at the exact balance scale equals the target. -/
theorem highLowBalance_low_exact (s r γ β : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    δ * (highLowBalanceScale s r γ β δ) ^ s * (paperLog δ) ^ γ =
      highLowEndpoint s r γ β δ := by
  unfold highLowBalanceScale highLowEndpoint
  calc
    _ = δ ^ (1 + (-(1 / (2 * (s + r)))) * s) *
        (paperLog δ) ^ (((β - γ) / (s + r)) * s + γ) := by
      convert rpow_product_balance δ (paperLog δ) 1 (-(1 / (2 * (s + r))))
        ((β - γ) / (s + r)) s γ hδ (paperLog_pos δ) using 1
      rw [Real.rpow_one]
    _ = _ := by
      have he₁ : 1 + (-(1 / (2 * (s + r)))) * s = highLowDensityExponent s r := by
        dsimp only [highLowDensityExponent]
        ring
      have he₂ : ((β - γ) / (s + r)) * s + γ = highLowLogExponent s r γ β := by
        dsimp only [highLowLogExponent]
        ring
      rw [he₁, he₂]

/-- The high contribution at the same scale equals exactly the same target. -/
theorem highLowBalance_high_exact {s r : ℝ} (hsr : s + r ≠ 0) (γ β : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    δ ^ (1 / 2 : ℝ) * (highLowBalanceScale s r γ β δ) ^ (-r) * (paperLog δ) ^ β =
      highLowEndpoint s r γ β δ := by
  unfold highLowBalanceScale highLowEndpoint
  rw [rpow_product_balance δ (paperLog δ) (1 / 2) (-(1 / (2 * (s + r))))
    ((β - γ) / (s + r)) (-r) β hδ (paperLog_pos δ)]
  have he₁ : 1 / 2 + (-(1 / (2 * (s + r)))) * (-r) = highLowDensityExponent s r := by
    dsimp only [highLowDensityExponent]
    field_simp
    ring
  have he₂ : ((β - γ) / (s + r)) * (-r) + β = highLowLogExponent s r γ β := by
    dsimp only [highLowLogExponent]
    field_simp
    ring
  rw [he₁, he₂]

theorem density_le_highLowEndpoint {s r γ β δ : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ ≤ highLowEndpoint s r γ β δ := by
  have hd : δ ≤ δ ^ highLowDensityExponent s r := by
    calc
      δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        (highLowDensityExponent_le_one hs.le hr)
  have hL : 1 ≤ (paperLog δ) ^ highLowLogExponent s r γ β :=
    Real.one_le_rpow (show 1 ≤ paperLog δ by have := paperLog_two_le δ; linarith)
      (highLowLogExponent_nonneg hs hr hγ hβ)
  exact hd.trans (by
    unfold highLowEndpoint
    nlinarith [Real.rpow_nonneg hδ.le (highLowDensityExponent s r)])

theorem highLowBalance_low_le_endpoint {s r γ β δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 < δ) :
    δ * (highLowBalanceScale s r γ β δ) ^ s ≤ highLowEndpoint s r γ β δ := by
  have hL : 1 ≤ (paperLog δ) ^ γ :=
    Real.one_le_rpow (show 1 ≤ paperLog δ by have := paperLog_two_le δ; linarith) hγ
  rw [← highLowBalance_low_exact s r γ β hδ]
  have hn : 0 ≤ δ * (highLowBalanceScale s r γ β δ) ^ s :=
    mul_nonneg hδ.le (Real.rpow_nonneg (highLowBalanceScale_pos s r γ β hδ).le _)
  nlinarith

noncomputable def highLowLogScale (s r : ℝ) : ℝ := 1 + 1 / (2 * (s + r))

theorem highLowLogScale_one_le {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    1 ≤ highLowLogScale s r := by
  dsimp only [highLowLogScale]
  have : 0 ≤ 1 / (2 * (s + r)) := by positivity
  linarith

theorem log_highLowBalanceScale_le {s r γ β δ : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hβγ : β ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (highLowBalanceScale s r γ β δ) ≤ highLowLogScale s r * paperLog δ := by
  have hu : 0 < s + r := by linarith
  have hh : (β - γ) / (s + r) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hu.le
  have hL : 0 ≤ Real.log (paperLog δ) :=
    Real.log_nonneg (show 1 ≤ paperLog δ by have := paperLog_two_le δ; linarith)
  have he : Real.log (highLowBalanceScale s r γ β δ) =
      (-(1 / (2 * (s + r)))) * Real.log δ +
        ((β - γ) / (s + r)) * Real.log (paperLog δ) := by
    rw [highLowBalanceScale, Real.log_mul
      (Real.rpow_pos_of_pos hδ _).ne' (Real.rpow_pos_of_pos (paperLog_pos δ) _).ne',
      Real.log_rpow hδ, Real.log_rpow (paperLog_pos δ)]
  rw [he]
  have hprod := mul_nonpos_of_nonpos_of_nonneg hh hL
  have hlog := paperLog_of_le_one hδ hδ1
  have hdiv : 0 < 1 / (2 * (s + r)) := by positivity
  dsimp only [highLowLogScale]
  nlinarith [paperLog_pos δ]

end PrimeSquares
