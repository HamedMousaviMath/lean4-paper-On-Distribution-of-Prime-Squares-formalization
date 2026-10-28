import PrimeSquares.HighLowEndpoint

/-!
# Operator norm inputs imply the B_N endpoint of Theorem 4.1

The input indicators are elements of genuine l¹ and l², with their exact
norms proved. The low operator maps l¹ to l∞ and the high operator maps l²
to l². Their norm bounds and decomposition imply the earlier indicator
predicate, so no scalar pairing estimate is assumed in the final theorem.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def finiteIndicator (F : Finset ℤ) (x : ℤ) : ℂ := if x ∈ F then 1 else 0

theorem finiteIndicator_mem_lp (F : Finset ℤ) (p : ENNReal) :
    Memℓp (finiteIndicator F) p := by
  have hz : Memℓp (finiteIndicator F) 0 := by
    apply memℓp_zero
    have he : {x : ℤ | finiteIndicator F x ≠ 0} = (F : Set ℤ) := by
      ext x
      simp only [finiteIndicator, ne_eq, Set.mem_ofPred_eq, mem_coe]
      split_ifs <;> simp_all
    rw [he]
    exact F.finite_toSet
  exact hz.of_exponent_ge (show (0 : ENNReal) ≤ p from zero_le)

noncomputable def finiteIndicatorLp (F : Finset ℤ) (p : ENNReal) :
    lp (fun _ : ℤ => ℂ) p := ⟨finiteIndicator F, finiteIndicator_mem_lp F p⟩

theorem finiteIndicator_inter (F I : Finset ℤ) (x : ℤ) :
    finiteIndicator (F ∩ I) x = if x ∈ I then finiteIndicator F x else 0 := by
  simp only [finiteIndicator, mem_inter]
  split_ifs <;> simp_all

theorem indicatorConvolution_as_tsum (K : ℤ → ℂ) (F : Finset ℤ) (x : ℤ) :
    indicatorConvolution K F x = ∑' y : ℤ, K (x - y) * finiteIndicator F y := by
  rw [tsum_eq_sum (s := F) (fun y hy => by simp only [finiteIndicator, ite_eq_right hy, mul_zero])]
  apply sum_congr rfl
  intro y hy
  simp only [finiteIndicator, ite_eq_left hy, mul_one]

theorem restrictedKernelPairing_as_tsum (K : ℤ → ℂ) (F G : Finset ℤ) :
    restrictedKernelPairing K F G =
      ∑' x : ℤ, indicatorConvolution K F x * star (finiteIndicator G x) := by
  rw [tsum_eq_sum (s := G) (fun x hx => by
    simp only [finiteIndicator, ite_eq_right hx, star_zero, mul_zero])]
  apply sum_congr rfl
  intro x hx
  simp only [finiteIndicator, ite_eq_left hx, star_one, mul_one]

theorem finiteIndicatorLp_norm (F : Finset ℤ) (p : ENNReal) (hp : 0 < p.toReal) :
    ‖finiteIndicatorLp F p‖ = (F.card : ℝ) ^ (1 / p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  have he : (∑' x : ℤ, ‖finiteIndicatorLp F p x‖ ^ p.toReal) = (F.card : ℝ) := by
    rw [tsum_eq_sum (s := F) (fun x hx => by
      simp only [finiteIndicatorLp, finiteIndicator, ite_eq_right hx, norm_zero,
        Real.zero_rpow hp.ne'])]
    calc
      _ = ∑ _ ∈ F, (1 : ℝ) := by
        apply sum_congr rfl
        intro x hx
        simp only [finiteIndicatorLp, finiteIndicator, ite_eq_left hx, norm_one, Real.one_rpow]
      _ = _ := by simp
  rw [he]

theorem finiteIndicatorLp_one_norm (F : Finset ℤ) :
    ‖finiteIndicatorLp F 1‖ = (F.card : ℝ) := by
  simpa only [ENNReal.toReal_one, div_one, Real.rpow_one] using
    finiteIndicatorLp_norm F 1 (by norm_num)

theorem finiteIndicatorLp_two_norm (F : Finset ℤ) :
    ‖finiteIndicatorLp F 2‖ = Real.sqrt (F.card : ℝ) := by
  simpa only [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow] using
    finiteIndicatorLp_norm F 2 (by norm_num)

/-- Actual normed-space formulation of the two decomposition inputs.
Linearity is unnecessary for the restricted endpoint, so it is not required. -/
def OperatorHighLowBound (K : ℤ → ℂ) (N J s r γ β C : ℝ) : Prop :=
  ∃ Lo : ℓ¹(ℤ, ℂ) → lp (fun _ : ℤ => ℂ) ⊤, ∃ Hi : ℓ²(ℤ, ℂ) → ℓ²(ℤ, ℂ),
    (∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x =
      Lo (finiteIndicatorLp F 1) x + Hi (finiteIndicatorLp F 2) x) ∧
    (∀ f : ℓ¹(ℤ, ℂ), ‖Lo f‖ ≤ C / N * J ^ s * (Real.log J) ^ γ * ‖f‖) ∧
    (∀ f : ℓ²(ℤ, ℂ), ‖Hi f‖ ≤ C * J ^ (-r) * (Real.log J) ^ β * ‖f‖)

theorem indicatorHighLowBound_of_operatorHighLowBound (K : ℤ → ℂ) (N J s r γ β C : ℝ)
    (h : OperatorHighLowBound K N J s r γ β C) : IndicatorHighLowBound K N J s r γ β C := by
  obtain ⟨Lo, Hi, heq, hlo, hhi⟩ := h
  intro F
  refine ⟨(fun x => Lo (finiteIndicatorLp F 1) x),
    Hi (finiteIndicatorLp F 2), heq F, ?_, ?_⟩
  · intro x
    have hnorm := lp.norm_apply_le_norm ENNReal.top_ne_zero
      (Lo (finiteIndicatorLp F 1)) x
    have hb := hlo (finiteIndicatorLp F 1)
    rw [finiteIndicatorLp_one_norm] at hb
    exact hnorm.trans hb
  · simpa only [finiteIndicatorLp_two_norm] using hhi (finiteIndicatorLp F 2)

theorem kernel_bound_of_local_indicator_bound (K : ℤ → ℂ) (windows : ℤ → Finset ℤ)
    (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ F : Finset ℤ, ∀ x, ‖indicatorConvolution K F x‖ ≤
      M * ((F ∩ windows x).card : ℝ)) : ∀ z, ‖K z‖ ≤ M := by
  intro z
  have hc : (({0} ∩ windows z).card : ℝ) ≤ 1 := by
    exact_mod_cast (show ({0} ∩ windows z).card ≤ 1 by
      simpa only [card_singleton] using card_le_card (inter_subset_left (s₂ := windows z) (s₁ := {0})))
  have hs : ‖K z‖ ≤ M * (({0} ∩ windows z).card : ℝ) := by
    simpa only [indicatorConvolution, sum_singleton, sub_zero] using h {0} z
  exact hs.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc hM)

/-- Full B_N clause of Theorem 4.1, including its local crude estimate and
actual operator norm inputs. The A_N clause remains a separate obligation. -/
theorem highLow_B_endpoint {s r γ β v C : ℝ}
    (hv : v < 1) (hsv : 1 - v ≤ s) (hr : 0 < r)
    (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℝ) (K : ℤ → ℂ) (windows : ℤ → Finset ℤ), 0 < N →
      (∀ F : Finset ℤ, ∀ x, ‖indicatorConvolution K F x‖ ≤
        C * N ^ (-v) * ‖finiteIndicatorLp (F ∩ windows x) 1‖) →
      (∀ k : ℕ, 2 ≤ (2 : ℝ) ^ k → (2 : ℝ) ^ k ≤ N ^ ((1 - v) / s) / 10 →
        OperatorHighLowBound K N ((2 : ℝ) ^ k) s r γ β C) →
      ∀ F G : Finset ℤ, (F.card : ℝ) * (G.card : ℝ) ≤ N ^ 2 →
        ‖restrictedKernelPairing K F G‖ / N ≤ D *
          ((finiteSetDensity N F G) ^ (1 - s / (2 * (s + r))) *
            (paperLog (finiteSetDensity N F G)) ^ (γ + s * (β - γ) / (s + r))) := by
  have hs : 0 < s := by linarith
  obtain ⟨D, hD, hd⟩ := restrictedKernelPairing_B_endpoint s r γ β C hs hr hβ hβγ hC
  refine ⟨D, hD, ?_⟩
  intro N K windows hN hlocal hdec F G hFG
  have hlocal' : ∀ F : Finset ℤ, ∀ x, ‖indicatorConvolution K F x‖ ≤
      C * N ^ (-v) * ((F ∩ windows x).card : ℝ) := by
    intro F x
    simpa only [finiteIndicatorLp_one_norm] using hlocal F x
  have hK : ∀ z, ‖K z‖ ≤ C * N ^ (-v) :=
    kernel_bound_of_local_indicator_bound K windows _ (by positivity) hlocal'
  exact hd N v K hN hK (fun k hk2 hkN =>
    indicatorHighLowBound_of_operatorHighLowBound K N ((2 : ℝ) ^ k) s r γ β C
      (hdec k hk2 hkN)) F G hFG

end PrimeSquares
