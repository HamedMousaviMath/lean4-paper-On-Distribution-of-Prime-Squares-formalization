import PrimeSquares.OrliczScalar

/-!
# The two density ranges for the A_N scalar estimate

The first range absorbs the B_N logarithmic bound after polynomial
domination. In the second range the actual dyadic choice is admissible and
controls all three scalar terms. The compact-density and operator pairing
bridges remain separate obligations; Theorem 4.1 is still partial.
-/

open Filter Topology

namespace PrimeSquares

theorem rpow_bound_of_power_cutoff {x L d a c : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L)
    (hd : 0 < d) (ha : 0 ≤ a) (hc : 0 < c) (hcut : d * x ^ c ≤ L) :
    x ^ a ≤ d ^ (-(a / c)) * L ^ (a / c) := by
  have hp : 0 ≤ a / c := div_nonneg ha hc.le
  have hxc : x ^ c ≤ L / d := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hcut)
  calc
    x ^ a = (x ^ c) ^ (a / c) := by rw [← Real.rpow_mul hx]; congr 1; field_simp
    _ ≤ (L / d) ^ (a / c) := Real.rpow_le_rpow (Real.rpow_nonneg hx _) hxc hp
    _ = d ^ (-(a / c)) * L ^ (a / c) := by
      rw [Real.div_rpow hL hd.le, Real.rpow_neg hd.le]
      ring

/-- The complementary density range in the source proof, with one uniform
constant and the exact Phi. theta and tau may be arbitrary real numbers. -/
theorem log_density_domination_le_orlicz {κ cstar a c d : ℝ}
    (hκ : 0 < κ) (hstar : 0 < cstar) (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 < d)
    (θ τ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ N δ : ℝ, 1 ≤ N → 0 < δ → δ ≤ 1 →
      d * (Real.log N) ^ c ≤ paperLog δ →
      (Real.log N) ^ a * δ ^ θ * (paperLog δ) ^ τ ≤ D * δ ^ θ * paperPhi cstar κ δ := by
  obtain ⟨D, hD, hΦ⟩ := paperLog_rpow_le_paperPhi hκ hstar (τ + a / c)
  refine ⟨d ^ (-(a / c)) * D, mul_pos (Real.rpow_pos_of_pos hd _) hD, ?_⟩
  intro N δ hN hδ _ hcut
  have hlog := Real.log_nonneg hN
  have hpow := rpow_bound_of_power_cutoff hlog (paperLog_pos δ).le hd ha hc hcut
  have hdδ : 0 ≤ δ ^ θ := Real.rpow_nonneg hδ.le _
  have hLτ : 0 ≤ (paperLog δ) ^ τ := Real.rpow_nonneg (paperLog_pos δ).le _
  calc
    _ ≤ (d ^ (-(a / c)) * (paperLog δ) ^ (a / c)) * δ ^ θ * (paperLog δ) ^ τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hdδ) hLτ
    _ = d ^ (-(a / c)) * δ ^ θ * (paperLog δ) ^ (τ + a / c) := by
      rw [Real.rpow_add (paperLog_pos δ)]
      ring
    _ ≤ d ^ (-(a / c)) * δ ^ θ * (D * paperPhi cstar κ δ) :=
      mul_le_mul_of_nonneg_left (hΦ δ) (mul_nonneg (Real.rpow_nonneg hd.le _) hdδ)
    _ = _ := by ring

theorem error_decay_factor_le_one {N A : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    (1 + Real.log N) ^ (-A) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.log_nonneg hN]) (by linarith)

theorem linear_log_scale_admissible {q : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hq : Tendsto (fun L => q L / L) atTop (𝓝 k)) (c₀ c : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℝ,
      L ≤ c₀ / (k + 1) * (Real.log N) ^ c → q L ≤ c₀ * (Real.log N) ^ c := by
  have he := hq.eventually (eventually_lt_nhds (show k < k + 1 by linarith))
  filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with L he hL
  intro N hcut
  have hk1 : 0 < k + 1 := by linarith
  have hqL : q L ≤ (k + 1) * L := ((div_lt_iff₀ (show 0 < L by linarith)).mp he).le
  calc
    _ ≤ (k + 1) * L := hqL
    _ ≤ (k + 1) * (c₀ / (k + 1) * (Real.log N) ^ c) :=
      mul_le_mul_of_nonneg_left hcut hk1.le
    _ = _ := by field_simp

/-- Small-density scalar branch with the actual source cutoff and actual
error decay factor. The index function is fixed before alpha, M, A and N;
only the eventual density threshold may depend on alpha and M. -/
theorem exists_admissible_dyadic_orlicz_bound {s r c₁ κ cstar : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hc₁ : 0 < c₁) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hstar : orliczLeadingCoefficient s r c₁ κ < cstar) (c₀ c : ℝ) :
    ∃ n : ℝ → ℕ, (∀ L : ℝ, 2 ≤ (2 : ℝ) ^ n L) ∧
      ∀ α M : ℝ, ∀ᶠ L : ℝ in atTop, ∀ N A : ℝ, 1 ≤ N → 0 ≤ A →
        L ≤ c₀ / (1 / (2 * (s + r)) + 1) * (Real.log N) ^ c →
        let δ := Real.exp (2 - L)
        let Q := (2 : ℝ) ^ n L
        Real.log Q ≤ c₀ * (Real.log N) ^ c ∧
        δ * Q ^ s * (Real.log Q) ^ α +
          δ ^ (1 / 2 : ℝ) * Q ^ (-r) *
            Real.exp (c₁ * (Real.log Q) ^ κ / Real.log (Real.log Q)) +
          δ ^ (1 / 2 : ℝ) * Q ^ (-r) * (Real.log Q) ^ M * (1 + Real.log N) ^ (-A) ≤
            3 * δ ^ highLowDensityExponent s r * paperPhi cstar κ δ := by
  obtain ⟨b, _, n, hn, hnup, hscalar⟩ := exists_dyadic_orlicz_scalar_bound hs hr hc₁ hκ0 hκ1 hstar
  have hk : 0 < 1 / (2 * (s + r)) := div_pos zero_lt_one (by linarith)
  have hadm := linear_log_scale_admissible hk (orliczLogScale_div_self_tendsto hκ1 _ b) c₀ c
  refine ⟨n, hn, ?_⟩
  intro α M
  filter_upwards [hscalar α M, hnup, hadm] with L hscalar hQup hadm
  intro N A hN hA hcut
  dsimp only
  have hQ : 0 < (2 : ℝ) ^ n L := pow_pos (by norm_num) _
  have hlogQ : Real.log ((2 : ℝ) ^ n L) ≤ orliczLogScale (1 / (2 * (s + r))) b κ L := by
    simpa only [Real.log_exp] using Real.log_le_log hQ hQup
  constructor
  · exact hlogQ.trans (hadm N hcut)
  · have he := error_decay_factor_le_one hN hA
    have hlog : 0 ≤ Real.log ((2 : ℝ) ^ n L) := Real.log_nonneg
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) (hn L))
    have hnonneg : 0 ≤ (Real.exp (2 - L)) ^ (1 / 2 : ℝ) *
        ((2 : ℝ) ^ n L) ^ (-r) * (Real.log ((2 : ℝ) ^ n L)) ^ M := by positivity
    have hterm := mul_le_mul_of_nonneg_left he hnonneg
    simp only [mul_one] at hterm
    exact (add_le_add le_rfl hterm).trans hscalar

end PrimeSquares
