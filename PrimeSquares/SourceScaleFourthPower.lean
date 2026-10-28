import PrimeSquares.SourceRangeMajorArc

open Filter
namespace PrimeSquares

theorem sqrt_le_half_of_four_le {n : ℝ} (hn : 4 ≤ n) : Real.sqrt n ≤ n/2 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by linarith,?_⟩
  nlinarith [mul_nonneg (by linarith : 0 ≤ n) (by linarith : 0 ≤ n-4)]

theorem sourceBudget_fourth_power {N R : ℝ} (hN : 4 ≤ N) (hR : 1 ≤ R)
    (hlog : 1 ≤ Real.log N) (hbudget : R^5*Real.log N ≤ Real.sqrt N) :
    R^4 ≤ N/2 := by
  have hp : R^4 ≤ R^5 := pow_le_pow_right₀ hR (by decide)
  have hm : R^5 ≤ R^5*Real.log N := by nlinarith [pow_nonneg (by linarith : 0 ≤ R) 5]
  exact hp.trans (hm.trans (hbudget.trans (sqrt_le_half_of_four_le hN)))

theorem inverse_rpow_from_fourth_power {x R a : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (hpow : R^4 ≤ x) : x^(-a) ≤ R^(-(4*a)) := by
  have h := Real.rpow_le_rpow_of_nonpos (pow_pos hR 4) hpow (neg_nonpos.mpr ha)
  rw [←Real.rpow_natCast R 4,←Real.rpow_mul hR.le] at h
  simpa only [Nat.cast_ofNat,mul_neg] using h

theorem sourceMajorArcScale_uniform_fourth_power {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
      (sourceMajorArcScale N Q)^4 ≤ (N : ℝ)/2 := by
  obtain ⟨N₁,_,hp⟩ := sourceMajorArc_parameter_threshold hc
  have he := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp he
  refine ⟨max 4 (max N₁ N₂),by omega,?_⟩
  intro N hN Q hQ hQl
  have hn1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hn2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hR,_,hb,_⟩ := hp N hn1 Q hQ hQl
  exact sourceBudget_fourth_power (by exact_mod_cast (by omega : 4 ≤ N)) hR (hN₂ N hn2) hb

end PrimeSquares
