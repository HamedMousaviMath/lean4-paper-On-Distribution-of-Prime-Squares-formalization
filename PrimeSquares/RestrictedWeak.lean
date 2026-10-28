import PrimeSquares.RestrictedImproving

/-!
# Actual restricted weak distribution bounds

For a nonnegative kernel, the global finite-set pairing bound controls the
cardinality of each superlevel set of the indicator output. Finiteness is
proved from the genuine l2 input. This is restricted weak type, not the
strong lp-to-lp' conclusion for general inputs.
-/

open Finset Filter Topology
open scoped lp

namespace PrimeSquares

theorem kernelL2Bound_superlevel_finite {K : ℤ → ℂ} {C : ℝ} (h2 : KernelL2Bound K C)
    (F : Finset ℤ) {level : ℝ} (hlevel : 0 < level) :
    Set.Finite {x : ℤ | level < ‖indicatorConvolution K F x‖} := by
  obtain ⟨T, heq, _⟩ := h2
  have hsum : Summable (fun x : ℤ => ‖T (finiteIndicatorLp F 2) x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (T (finiteIndicatorLp F 2))).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have he : ∀ᶠ x : ℤ in cofinite, ‖T (finiteIndicatorLp F 2) x‖ ^ 2 < level ^ 2 :=
    hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds (sq_pos_of_pos hlevel))
  have hf : Set.Finite {x : ℤ | ¬ ‖T (finiteIndicatorLp F 2) x‖ ^ 2 < level ^ 2} :=
    mem_cofinite.mp he
  apply hf.subset
  intro x hx
  change level < ‖indicatorConvolution K F x‖ at hx
  rw [heq F x] at hx
  change ¬ ‖T (finiteIndicatorLp F 2) x‖ ^ 2 < level ^ 2
  nlinarith [norm_nonneg (T (finiteIndicatorLp F 2) x)]

theorem positive_superlevel_pairing_lower {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    (F E : Finset ℤ) (level : ℝ) (hE : ∀ x ∈ E, level < ‖indicatorConvolution K F x‖) :
    level * (E.card : ℝ) ≤ ‖restrictedKernelPairing K F E‖ := by
  rw [restrictedKernelPairing_norm_positive hK]
  calc
    _ = ∑ _ ∈ E, level := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro x hx
      have hnorm := complex_norm_eq_re (indicatorConvolution_im_zero hK F x)
        (indicatorConvolution_re_nonneg hK F x)
      simpa only [hnorm] using (hE x hx).le

/-- Restricted weak gauge bound for the exact finite superlevel set. -/
theorem restricted_positive_weak_bound {K : ℤ → ℂ} {p S CTwo : ℝ}
    (hK : NonnegativeKernel K) (hp : 1 < p) (hS : 0 ≤ S) (h2 : KernelL2Bound K CTwo)
    (hpair : ∀ F G : Finset ℤ, ‖restrictedKernelPairing K F G‖ ≤
      S * (F.card : ℝ) ^ (1 / p) * (G.card : ℝ) ^ (1 / p))
    (F : Finset ℤ) {level : ℝ} (hlevel : 0 < level) :
    ∃ E : Finset ℤ, (∀ x : ℤ, x ∈ E ↔ level < ‖indicatorConvolution K F x‖) ∧
      level * (E.card : ℝ) ^ (1 / holderConjugate p) ≤ S * (F.card : ℝ) ^ (1 / p) := by
  classical
  let hf := kernelL2Bound_superlevel_finite h2 F hlevel
  let E := hf.toFinset
  have hE : ∀ x : ℤ, x ∈ E ↔ level < ‖indicatorConvolution K F x‖ := by
    intro x
    exact hf.mem_toFinset
  refine ⟨E, hE, ?_⟩
  by_cases hz : E = ∅
  · have hq : 0 < 1 / holderConjugate p := one_div_pos.mpr (holderConjugate_pos hp)
    rw [hz, card_empty, Nat.cast_zero, Real.zero_rpow hq.ne', mul_zero]
    exact mul_nonneg hS (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have he : (0 : ℝ) < E.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hz)
  have hlower := positive_superlevel_pairing_lower hK F E level (fun x hx => (hE x).mp hx)
  have hbound := hlower.trans (hpair F E)
  have hsum : 1 / holderConjugate p + 1 / p = 1 := by rw [holderConjugate_reciprocal hp]; ring
  have hprod : (E.card : ℝ) ^ (1 / holderConjugate p) * (E.card : ℝ) ^ (1 / p) = E.card := by
    rw [← Real.rpow_add he, hsum, Real.rpow_one]
  apply (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos he (1 / p))).mp
  calc
    _ = level * (E.card : ℝ) := by rw [mul_assoc, hprod]
    _ ≤ _ := hbound

theorem weak_gauge_to_cardinality {p level B e : ℝ} (hp : 1 < p) (hlevel : 0 < level) (he : 0 ≤ e)
    (h : level * e ^ (1 / holderConjugate p) ≤ B) : e ≤ (B / level) ^ holderConjugate p := by
  have hq := holderConjugate_pos hp
  have hh : e ^ (1 / holderConjugate p) ≤ B / level :=
    (le_div_iff₀ hlevel).mpr (by simpa only [mul_comm] using h)
  calc
    e = (e ^ (1 / holderConjugate p)) ^ holderConjugate p := by
      rw [← Real.rpow_mul he, one_div_mul_cancel hq.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg he _) hh hq.le

/-- Both kernels have a genuine restricted weak distribution estimate.
The source's positivity of A_N is included for this distribution step. -/
theorem highLow_AB_restricted_weak
    {v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr p CTwoA CTwoB : ℝ}
    (hv : v < 1) (hsv : 1 - v ≤ s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hCB : 0 < CB) (ha : 0 ≤ a) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : 0 < c)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hp : improvingCriticalExponent s r < p) (hp2 : p ≤ 2)
    (hTwoA : 0 ≤ CTwoA) (hTwoB : 0 ≤ CTwoB) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N : ℝ) (KA KB : ℤ → ℂ) (windows : ℤ → Finset ℤ), 0 < N →
        HighLowEndpointInputs KA KB windows N v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr →
        KernelL2Bound KA CTwoA → KernelL2Bound KB CTwoB → NonnegativeKernel KA →
        ∀ (F : Finset ℤ) (level : ℝ), 0 < level →
          (∃ EA : Finset ℤ, (∀ x : ℤ, x ∈ EA ↔ level < ‖indicatorConvolution KA F x‖) ∧
            level * (EA.card : ℝ) ^ (1 / holderConjugate p) ≤
              D * N ^ (1 / holderConjugate p - 1 / p) * (F.card : ℝ) ^ (1 / p)) ∧
          (∃ EB : Finset ℤ, (∀ x : ℤ, x ∈ EB ↔ level < ‖indicatorConvolution KB F x‖) ∧
            level * (EB.card : ℝ) ^ (1 / holderConjugate p) ≤
              D * N ^ (1 / holderConjugate p - 1 / p) * (F.card : ℝ) ^ (1 / p)) := by
  have hs : 0 < s := by linarith
  have hp1 : 1 < p := (improvingCriticalExponent_one_lt hs hr).trans hp
  obtain ⟨D, hD, hglobal⟩ := highLow_AB_restricted_improving hv hsv hr hβ hβγ hCB ha hc₀ hc₁ hc
    hκ0 hκ1 hp hp2 hTwoA hTwoB
  refine ⟨D, hD, ?_⟩
  intro N KA KB windows hN H h2A h2B hKA F level hlevel
  have hS : 0 ≤ D * N ^ (1 / holderConjugate p - 1 / p) :=
    mul_nonneg hD.le (Real.rpow_nonneg hN.le _)
  have hpa : ∀ F G : Finset ℤ, ‖restrictedKernelPairing KA F G‖ ≤
      (D * N ^ (1 / holderConjugate p - 1 / p)) * (F.card : ℝ) ^ (1 / p) * (G.card : ℝ) ^ (1 / p) := by
    intro F G
    exact (le_add_of_nonneg_right (norm_nonneg (restrictedKernelPairing KB F G))).trans
      (hglobal N KA KB windows hN H h2A h2B F G)
  have hpb : ∀ F G : Finset ℤ, ‖restrictedKernelPairing KB F G‖ ≤
      (D * N ^ (1 / holderConjugate p - 1 / p)) * (F.card : ℝ) ^ (1 / p) * (G.card : ℝ) ^ (1 / p) := by
    intro F G
    exact (le_add_of_nonneg_left (norm_nonneg (restrictedKernelPairing KA F G))).trans
      (hglobal N KA KB windows hN H h2A h2B F G)
  exact ⟨restricted_positive_weak_bound hKA hp1 hS h2A hpa F hlevel,
    restricted_positive_weak_bound H.nonnegative hp1 hS h2B hpb F hlevel⟩

end PrimeSquares
