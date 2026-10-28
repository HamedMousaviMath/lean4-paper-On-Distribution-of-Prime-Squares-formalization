import PrimeSquares.RestrictedL2

/-!
# Global restricted improving for both actual kernels

Source: e:restrictedimproving, equation 4.17, inside Corollary 4.15.
The endpoint and genuine l2 hypotheses imply the exact unnormalized
restricted pairing estimate for all finite sets. Strong interpolation for
general lp inputs remains a separate obligation.
-/

open Finset

namespace PrimeSquares

theorem highLow_AB_power_small {v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr p : ℝ}
    (hv : v < 1) (hsv : 1 - v ≤ s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hCB : 0 < CB) (ha : 0 ≤ a) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : 0 < c)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hp : improvingCriticalExponent s r < p) :
    ∃ DB : ℝ, 0 < DB ∧ ∃ DA : ℝ, 0 < DA ∧
      ∀ (N : ℝ) (KA KB : ℤ → ℂ) (windows : ℤ → Finset ℤ), 0 < N →
        HighLowEndpointInputs KA KB windows N v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr →
        ∀ F G : Finset ℤ, (F.card : ℝ) * (G.card : ℝ) ≤ N ^ 2 →
          ‖restrictedKernelPairing KB F G‖ / N ≤ DB * (finiteSetDensity N F G) ^ (1 / p) ∧
          ‖restrictedKernelPairing KA F G‖ / N ≤ DA * (finiteSetDensity N F G) ^ (1 / p) := by
  have hs : 0 < s := by linarith
  have hp1 : 1 < p := (improvingCriticalExponent_one_lt hs hr).trans hp
  have hσ : 0 < 1 / p := one_div_pos.mpr (by linarith)
  have hgap : 1 / p < highLowDensityExponent s r := by
    have := improving_reciprocal_gap hs hr hp
    linarith
  let cstar : ℝ := orliczLeadingCoefficient s r c₁ κ + 1
  have hstar : orliczLeadingCoefficient s r c₁ κ < cstar := by dsimp [cstar]; linarith
  have hcstar : 0 ≤ cstar := by
    have := orliczLeadingCoefficient_pos hs hr hc₁ κ
    dsimp [cstar]
    linarith
  obtain ⟨DLB, hDLB, hLB⟩ := density_power_log_loss_nonneg hσ hgap (highLowLogExponent s r γ β)
  obtain ⟨DLA, hDLA, hLA⟩ := density_power_phi_loss_nonneg hκ0.le hκ1 hcstar hσ hgap
  obtain ⟨DB, hDB, DA, hDA, hend⟩ := highLow_AB_endpoint hv hsv hr hβ hβγ hCB ha hc₀ hc₁ hc hκ0 hκ1 hstar
  refine ⟨DB * DLB, mul_pos hDB hDLB, DA * DLA, mul_pos hDA hDLA, ?_⟩
  intro N KA KB windows hN H F G hFG
  obtain ⟨hB, hA⟩ := hend N KA KB windows hN H F G hFG
  have hδ : 0 ≤ finiteSetDensity N F G :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hδ1 : finiteSetDensity N F G ≤ 1 := (div_le_one (sq_pos_of_pos hN)).mpr hFG
  constructor
  · have hb := mul_le_mul_of_nonneg_left (hLB _ hδ hδ1) hDB.le
    exact hB.trans (by simpa only [highLowDensityExponent, highLowLogExponent, mul_assoc] using hb)
  · have ha := mul_le_mul_of_nonneg_left (hLA _ hδ hδ1) hDA.le
    exact hA.trans (by simpa only [highLowDensityExponent, mul_assoc] using ha)

/-- Equation 4.17, with the sum of both pairings and all finite sets.
The additional l2 hypotheses are actual continuous linear operators.
The strong lp estimate of Corollary 4.15 is not asserted here. -/
theorem highLow_AB_restricted_improving
    {v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr p CTwoA CTwoB : ℝ}
    (hv : v < 1) (hsv : 1 - v ≤ s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hCB : 0 < CB) (ha : 0 ≤ a) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : 0 < c)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hp : improvingCriticalExponent s r < p) (hp2 : p ≤ 2)
    (hTwoA : 0 ≤ CTwoA) (hTwoB : 0 ≤ CTwoB) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N : ℝ) (KA KB : ℤ → ℂ) (windows : ℤ → Finset ℤ), 0 < N →
        HighLowEndpointInputs KA KB windows N v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr →
        KernelL2Bound KA CTwoA → KernelL2Bound KB CTwoB →
        ∀ F G : Finset ℤ,
          ‖restrictedKernelPairing KA F G‖ + ‖restrictedKernelPairing KB F G‖ ≤
            D * N ^ (1 / holderConjugate p - 1 / p) * (F.card : ℝ) ^ (1 / p) *
              (G.card : ℝ) ^ (1 / p) := by
  have hs : 0 < s := by linarith
  have hp1 : 1 < p := (improvingCriticalExponent_one_lt hs hr).trans hp
  have hp0 : 0 < p := by linarith
  obtain ⟨DB, hDB, DA, hDA, hsmall⟩ := highLow_AB_power_small hv hsv hr hβ hβγ hCB
    ha hc₀ hc₁ hc hκ0 hκ1 hp
  let D := (DA + CTwoA) + (DB + CTwoB)
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro N KA KB windows hN H h2A h2B F G
  have hga := restricted_pairing_globalization hN hp0 hp2 hDA.le hTwoA h2A
    (fun F G hFG => (hsmall N KA KB windows hN H F G hFG).2) F G
  have hgb := restricted_pairing_globalization hN hp0 hp2 hDB.le hTwoB h2B
    (fun F G hFG => (hsmall N KA KB windows hN H F G hFG).1) F G
  have hsum : (‖restrictedKernelPairing KA F G‖ + ‖restrictedKernelPairing KB F G‖) / N ≤
      D * (finiteSetDensity N F G) ^ (1 / p) := by
    rw [add_div]
    exact (add_le_add hga hgb).trans_eq (by dsimp [D]; ring)
  exact density_denormalize_bound hN hp1 F G hsum

end PrimeSquares
