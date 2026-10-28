import PrimeSquares.OrliczGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Leading coefficient of the A_N balance

The literal high-term denominator is log(log Q), without an additive two.
Here q denotes log Q and L denotes Log delta. The scaling theorem below
relates that literal expression to the exact weight in the paper's Phi.
The uniform finite-scale A_N endpoint is a subsequent obligation.
-/

open Filter Topology

namespace PrimeSquares

noncomputable def orliczLogScale (k b κ L : ℝ) : ℝ :=
  k * L + b * orliczWeight κ L

theorem orliczLogScale_div_self_tendsto {κ : ℝ} (hκ : κ < 1) (k b : ℝ) :
    Tendsto (fun L : ℝ => orliczLogScale k b κ L / L) atTop (𝓝 k) := by
  have h := ((orliczWeight_div_self_tendsto hκ).const_mul b).const_add k
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  dsimp [orliczLogScale]
  field_simp

theorem log_ratio_of_linear_ratio {q : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hq : Tendsto (fun L => q L / L) atTop (𝓝 k)) :
    Tendsto (fun L => Real.log (q L) / Real.log L) atTop (𝓝 1) := by
  have he : ∀ᶠ L : ℝ in atTop, 0 < q L / L :=
    hq.eventually (eventually_gt_nhds hk)
  have hz := (hq.log hk.ne').div_atTop Real.tendsto_log_atTop
  have h := hz.const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with L hqL hL
  have hL0 : 0 < L := by linarith
  have hq0 : 0 < q L := by simpa only [zero_mul] using (lt_div_iff₀ hL0).mp hqL
  rw [Real.log_div hq0.ne' hL0.ne']
  field_simp [ne_of_gt (Real.log_pos hL)]
  ring

/-- Exact leading ratio for the literal high exponential in Theorem 4.1.
No asymptotic equivalence is assumed about either logarithmic denominator. -/
theorem high_weight_ratio_tendsto {q : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hq : Tendsto (fun L => q L / L) atTop (𝓝 k)) (κ : ℝ) :
    Tendsto (fun L => ((q L) ^ κ / Real.log (q L)) / orliczWeight κ L)
      atTop (𝓝 (k ^ κ)) := by
  have hlog := log_ratio_of_linear_ratio hk hq
  have hn : Tendsto (fun L : ℝ => 2 / Real.log L + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using (Real.tendsto_log_atTop.const_div_atTop 2).add_const 1
  have h := (hq.rpow_const (p := κ) (Or.inl hk.ne')).mul (hn.div hlog one_ne_zero)
  simp only [div_self one_ne_zero, mul_one] at h
  apply h.congr'
  have he : ∀ᶠ L : ℝ in atTop, 0 < q L / L :=
    hq.eventually (eventually_gt_nhds hk)
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with L hqL hL
  have hL0 : 0 < L := by linarith
  have hq0 : 0 < q L := by simpa only [zero_mul] using (lt_div_iff₀ hL0).mp hqL
  have hp := ne_of_gt (Real.rpow_pos_of_pos hL0 κ)
  have hlogL := ne_of_gt (Real.log_pos hL)
  have hd : 2 + Real.log L ≠ 0 := by linarith [Real.log_pos hL]
  rw [Real.div_rpow hq0.le hL0.le, orliczWeight]
  dsimp only [Pi.div_apply]
  field_simp

theorem orliczLogScale_high_weight_ratio {κ k : ℝ} (hκ : κ < 1) (hk : 0 < k) (b : ℝ) :
    Tendsto (fun L => ((orliczLogScale k b κ L) ^ κ /
      Real.log (orliczLogScale k b κ L)) / orliczWeight κ L) atTop (𝓝 (k ^ κ)) :=
  high_weight_ratio_tendsto hk (orliczLogScale_div_self_tendsto hκ k b) κ

theorem orliczLogScale_tendsto_atTop {κ k : ℝ} (hκ : κ < 1) (hk : 0 < k) (b : ℝ) :
    Tendsto (orliczLogScale k b κ) atTop atTop := by
  apply ((orliczLogScale_div_self_tendsto hκ k b).pos_mul_atTop hk tendsto_id).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact div_mul_cancel₀ _ hL.ne'

/-- There is an actual dyadic scale, rounded down from exp(kL+bW).
Rounding changes the normalized logarithmic correction by a term tending
to zero. No regularity assumption on the chosen index function is needed. -/
theorem exists_dyadic_orlicz_scale {κ k : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hk : 0 < k) (b : ℝ) :
    ∃ n : ℝ → ℕ, (∀ L : ℝ, 2 ≤ (2 : ℝ) ^ n L) ∧
      (∀ᶠ L : ℝ in atTop, (2 : ℝ) ^ n L ≤ Real.exp (orliczLogScale k b κ L)) ∧
      Tendsto (fun L => (Real.log ((2 : ℝ) ^ n L) - k * L) / orliczWeight κ L)
        atTop (𝓝 b) := by
  classical
  have hall : ∀ L : ℝ, ∃ n : ℕ, 2 ≤ (2 : ℝ) ^ n ∧
      (2 ≤ Real.exp (orliczLogScale k b κ L) →
        (2 : ℝ) ^ n ≤ Real.exp (orliczLogScale k b κ L) ∧
        Real.exp (orliczLogScale k b κ L) < 2 * (2 : ℝ) ^ n) := by
    intro L
    by_cases hL : 2 ≤ Real.exp (orliczLogScale k b κ L)
    · obtain ⟨n, hn, hnle, hnlt⟩ := exists_dyadic_below hL
      exact ⟨n, hn, fun _ => ⟨hnle, hnlt⟩⟩
    · exact ⟨1, by norm_num, fun h => (hL h).elim⟩
  choose n hn using hall
  have he : ∀ᶠ L : ℝ in atTop, 2 ≤ Real.exp (orliczLogScale k b κ L) :=
    (Real.tendsto_exp_atTop.comp (orliczLogScale_tendsto_atTop hκ1 hk b)).eventually_ge_atTop 2
  have hround : ∀ᶠ L : ℝ in atTop,
      |Real.log ((2 : ℝ) ^ n L) - orliczLogScale k b κ L| ≤ Real.log 2 := by
    filter_upwards [he] with L hL
    have hQ : 0 < (2 : ℝ) ^ n L := pow_pos (by norm_num) _
    have hu := Real.log_le_log hQ (hn L |>.2 hL).1
    have hl := Real.log_lt_log (Real.exp_pos _) (hn L |>.2 hL).2
    rw [Real.log_exp] at hu
    rw [Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQ.ne'] at hl
    apply abs_le.mpr
    constructor
    · linarith
    · linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h := (bounded_div_orliczWeight_tendsto hκ0 hround).const_add b
  simp only [add_zero] at h
  refine ⟨n, fun L => (hn L).1, he.mono (fun L hL => (hn L |>.2 hL).1), ?_⟩
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  have hw := (orliczWeight_pos κ hL).ne'
  dsimp [orliczLogScale]
  field_simp
  ring

theorem linear_ratio_of_orlicz_correction {κ k b : ℝ} {q : ℝ → ℝ}
    (hκ : κ < 1)
    (hq : Tendsto (fun L => (q L - k * L) / orliczWeight κ L) atTop (𝓝 b)) :
    Tendsto (fun L => q L / L) atTop (𝓝 k) := by
  have h := (hq.mul (orliczWeight_div_self_tendsto hκ)).const_add k
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  have hw := (orliczWeight_pos κ hL).ne'
  field_simp
  ring

theorem log_scaled_div_orliczWeight_tendsto {κ k : ℝ} {q : ℝ → ℝ}
    (hκ : 0 < κ) (hk : 0 < k) (hq : Tendsto (fun L => q L / L) atTop (𝓝 k)) :
    Tendsto (fun L => Real.log (q L) / orliczWeight κ L) atTop (𝓝 0) := by
  have h := (log_ratio_of_linear_ratio hk hq).mul (log_div_orliczWeight_tendsto hκ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  field_simp [ne_of_gt (Real.log_pos hL)]

noncomputable def orliczLeadingCoefficient (s r c₁ κ : ℝ) : ℝ :=
  c₁ * s / ((2 : ℝ) ^ κ * (s + r) ^ (κ + 1))

theorem orliczLeadingCoefficient_eq {s r : ℝ} (hsr : 0 < s + r) (c₁ κ : ℝ) :
    orliczLeadingCoefficient s r c₁ κ =
      s * (c₁ * (1 / (2 * (s + r))) ^ κ / (s + r)) := by
  rw [orliczLeadingCoefficient, Real.div_rpow zero_le_one
    (mul_nonneg (by norm_num) hsr.le), Real.one_rpow,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsr.le,
    Real.rpow_add hsr, Real.rpow_one]
  field_simp

/-- Every coefficient strictly above the printed leading one leaves strict
margins for the low, high and polynomial error contributions. -/
theorem exists_orlicz_balance_margin {s r c₁ κ cstar : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hc₁ : 0 < c₁)
    (hstar : orliczLeadingCoefficient s r c₁ κ < cstar) :
    ∃ b : ℝ, 0 < b ∧ s * b < cstar ∧
      c₁ * (1 / (2 * (s + r))) ^ κ - r * b < cstar ∧ -r * b < cstar := by
  have hsr : 0 < s + r := by linarith
  let b₀ : ℝ := c₁ * (1 / (2 * (s + r))) ^ κ / (s + r)
  have hb₀ : 0 < b₀ := div_pos (mul_pos hc₁ (Real.rpow_pos_of_pos
    (div_pos zero_lt_one (by linarith)) _)) hsr
  have hgap : b₀ < cstar / s := by
    apply (lt_div_iff₀ hs).mpr
    rw [orliczLeadingCoefficient_eq hsr c₁ κ] at hstar
    simpa only [b₀, mul_comm] using hstar
  obtain ⟨b, hb, hbs⟩ := exists_between hgap
  have hsb : s * b < cstar := by
    have := (lt_div_iff₀ hs).mp hbs
    linarith
  have hleading : c₁ * (1 / (2 * (s + r))) ^ κ < (s + r) * b := by
    have := (div_lt_iff₀ hsr).mp hb
    linarith
  refine ⟨b, hb₀.trans hb, hsb, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_pos hr (hb₀.trans hb)]

theorem orlicz_low_exponent_ratio_tendsto {κ k b : ℝ} {q : ℝ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hk : 0 < k)
    (hq : Tendsto (fun L => (q L - k * L) / orliczWeight κ L) atTop (𝓝 b))
    (s α d : ℝ) :
    Tendsto (fun L => (s * (q L - k * L) + α * Real.log (q L) + d) /
      orliczWeight κ L) atTop (𝓝 (s * b)) := by
  have hl := log_scaled_div_orliczWeight_tendsto hκ0 hk (linear_ratio_of_orlicz_correction hκ1 hq)
  have h := ((hq.const_mul s).add (hl.const_mul α)).add
    ((inv_orliczWeight_tendsto hκ0).const_mul d)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun L => by dsimp; ring

theorem orlicz_high_exponent_ratio_tendsto {κ k b : ℝ} {q : ℝ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hk : 0 < k)
    (hq : Tendsto (fun L => (q L - k * L) / orliczWeight κ L) atTop (𝓝 b))
    (r c₁ d : ℝ) :
    Tendsto (fun L => (-r * (q L - k * L) + c₁ * (q L) ^ κ / Real.log (q L) + d) /
      orliczWeight κ L) atTop (𝓝 (c₁ * k ^ κ - r * b)) := by
  have hh := high_weight_ratio_tendsto hk (linear_ratio_of_orlicz_correction hκ1 hq) κ
  have h := ((hq.const_mul (-r)).add (hh.const_mul c₁)).add
    ((inv_orliczWeight_tendsto hκ0).const_mul d)
  simp only [mul_zero, add_zero] at h
  have he : -r * b + c₁ * k ^ κ = c₁ * k ^ κ - r * b := by ring
  rw [he] at h
  apply h.congr'
  exact Eventually.of_forall fun L => by dsimp; ring

/-- The sharp epsilon coefficient controls all three A_N contributions at
an actual dyadic scale. This is an asymptotic scalar balance, not yet the
uniform endpoint with the N-dependent admissibility condition. -/
theorem exists_dyadic_orlicz_balance {s r c₁ κ cstar : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hc₁ : 0 < c₁) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hstar : orliczLeadingCoefficient s r c₁ κ < cstar) :
    ∃ b : ℝ, 0 < b ∧ ∃ n : ℝ → ℕ,
      (∀ L : ℝ, 2 ≤ (2 : ℝ) ^ n L) ∧
      (∀ᶠ L : ℝ in atTop, (2 : ℝ) ^ n L ≤
        Real.exp (orliczLogScale (1 / (2 * (s + r))) b κ L)) ∧
      ∀ α M : ℝ, ∀ᶠ L : ℝ in atTop,
        let k := 1 / (2 * (s + r))
        let q := Real.log ((2 : ℝ) ^ n L)
        s * (q - k * L) + α * Real.log q + 2 * s * k ≤ cstar * orliczWeight κ L ∧
        -r * (q - k * L) + c₁ * q ^ κ / Real.log q - 2 * r * k ≤ cstar * orliczWeight κ L ∧
        -r * (q - k * L) + M * Real.log q - 2 * r * k ≤ cstar * orliczWeight κ L := by
  obtain ⟨b, hb, hlo, hhi, herr⟩ := exists_orlicz_balance_margin hs hr hc₁ hstar
  have hk : 0 < 1 / (2 * (s + r)) := div_pos zero_lt_one (by linarith)
  obtain ⟨n, hn, hnup, hcorr⟩ := exists_dyadic_orlicz_scale hκ0 hκ1 hk b
  refine ⟨b, hb, n, hn, hnup, ?_⟩
  intro α M
  have hl := (orlicz_low_exponent_ratio_tendsto hκ0 hκ1 hk hcorr s α
    (2 * s * (1 / (2 * (s + r))))).eventually (eventually_lt_nhds hlo)
  have hh := (orlicz_high_exponent_ratio_tendsto hκ0 hκ1 hk hcorr r c₁
    (-2 * r * (1 / (2 * (s + r))))).eventually (eventually_lt_nhds hhi)
  have he := (orlicz_low_exponent_ratio_tendsto hκ0 hκ1 hk hcorr (-r) M
    (-2 * r * (1 / (2 * (s + r))))).eventually (eventually_lt_nhds herr)
  filter_upwards [hl, hh, he, eventually_ge_atTop (2 : ℝ)] with L hl hh he hL
  have hw := orliczWeight_pos κ hL
  dsimp only
  constructor
  · exact ((div_lt_iff₀ hw).mp hl).le
  constructor
  · convert ((div_lt_iff₀ hw).mp hh).le using 1
    ring
  · convert ((div_lt_iff₀ hw).mp he).le using 1
    ring

end PrimeSquares
