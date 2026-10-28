import PrimeSquares.HighLowOptimization
import PrimeSquares.HighLowPairing

/-!
# The B_N endpoint for actual finite-set convolution pairings

Source: Theorem 4.1, equation `e:endimprovbn`. The decomposition hypotheses
below are precisely the indicator-output consequences of the paper's
l¹->l∞ and l²->l² norm assumptions. The high output lives in genuine l².
The convolution kernel, finite-set pairing, density and normalizations are
explicit. The A_N conclusion of Theorem 4.1 is not asserted by this module.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def finiteSetDensity (N : ℝ) (F G : Finset ℤ) : ℝ :=
  (F.card : ℝ) * (G.card : ℝ) / N ^ 2

/-- The needed restriction of the operator decomposition to indicator inputs.
The witnesses are output functions; no linearity or kernel property of the
pieces is needed for the restricted pairing conclusion. -/
def IndicatorHighLowBound (K : ℤ → ℂ) (N J s r γ β C : ℝ) : Prop :=
  ∀ F : Finset ℤ, ∃ lo : ℤ → ℂ, ∃ hi : ℓ²(ℤ, ℂ),
    (∀ x, indicatorConvolution K F x = lo x + hi x) ∧
    (∀ x, ‖lo x‖ ≤ C / N * J ^ s * (Real.log J) ^ γ * (F.card : ℝ)) ∧
    ‖hi‖ ≤ C * J ^ (-r) * (Real.log J) ^ β * Real.sqrt (F.card : ℝ)

theorem normalized_pairing_terms (N f g A B C : ℝ) (hN : 0 < N)
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (g * (C / N * A * f) + (C * B * Real.sqrt f) * Real.sqrt g) / N =
      C * ((f * g / N ^ 2) * A + (f * g / N ^ 2) ^ (1 / 2 : ℝ) * B) := by
  have he : (f * g / N ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt f * Real.sqrt g / N := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (mul_nonneg hf hg),
      Real.sqrt_mul hf, Real.sqrt_sq hN.le]
  rw [he]
  field_simp

theorem restrictedKernelPairing_decomposition_bound (K : ℤ → ℂ)
    (N J s r γ β C : ℝ) (hN : 0 < N)
    (hdec : IndicatorHighLowBound K N J s r γ β C) (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ / N ≤
      C * (finiteSetDensity N F G * J ^ s * (Real.log J) ^ γ +
        (finiteSetDensity N F G) ^ (1 / 2 : ℝ) * J ^ (-r) * (Real.log J) ^ β) := by
  obtain ⟨lo, hi, heq, hlo, hhi⟩ := hdec F
  have h := finite_highLow_pairing_bound G (indicatorConvolution K F) lo hi
    (C / N * J ^ s * (Real.log J) ^ γ * (F.card : ℝ)) (fun x _ => heq x) (fun x _ => hlo x)
  have hn : ‖restrictedKernelPairing K F G‖ ≤
      (G.card : ℝ) * (C / N * J ^ s * (Real.log J) ^ γ * (F.card : ℝ)) +
        (C * J ^ (-r) * (Real.log J) ^ β * Real.sqrt (F.card : ℝ)) * Real.sqrt (G.card : ℝ) := by
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hhi (Real.sqrt_nonneg _)))
  calc
    _ ≤ ((G.card : ℝ) * (C / N * J ^ s * (Real.log J) ^ γ * (F.card : ℝ)) +
        (C * J ^ (-r) * (Real.log J) ^ β * Real.sqrt (F.card : ℝ)) * Real.sqrt (G.card : ℝ)) / N :=
      div_le_div_of_nonneg_right hn hN.le
    _ = _ := by
      have he := normalized_pairing_terms N (F.card : ℝ) (G.card : ℝ)
        (J ^ s * (Real.log J) ^ γ) (J ^ (-r) * (Real.log J) ^ β) C hN
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      simpa only [finiteSetDensity, mul_assoc] using he

theorem restrictedKernelPairing_crude_normalized (K : ℤ → ℂ) (N v C : ℝ)
    (hN : 0 < N) (hK : ∀ z, ‖K z‖ ≤ C * N ^ (-v)) (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ / N ≤ C * finiteSetDensity N F G * N ^ (1 - v) := by
  calc
    _ ≤ ((F.card : ℝ) * (G.card : ℝ) * (C * N ^ (-v))) / N :=
      div_le_div_of_nonneg_right (restrictedKernelPairing_norm_le K F G _ hK) hN.le
    _ = _ := by
      rw [finiteSetDensity, Real.rpow_neg hN.le, Real.rpow_sub hN, Real.rpow_one]
      field_simp

/-- The complete B_N restricted endpoint for any positive scale N. The
paper's stronger assumptions on v and s are not needed once these two norm
inputs and their matching cutoff are available. -/
theorem restrictedKernelPairing_B_endpoint (s r γ β C : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N v : ℝ) (K : ℤ → ℂ), 0 < N →
      (∀ z, ‖K z‖ ≤ C * N ^ (-v)) →
      (∀ k : ℕ, 2 ≤ (2 : ℝ) ^ k → (2 : ℝ) ^ k ≤ N ^ ((1 - v) / s) / 10 →
        IndicatorHighLowBound K N ((2 : ℝ) ^ k) s r γ β C) →
      ∀ F G : Finset ℤ, (F.card : ℝ) * (G.card : ℝ) ≤ N ^ 2 →
        ‖restrictedKernelPairing K F G‖ / N ≤ D * highLowEndpoint s r γ β (finiteSetDensity N F G) := by
  refine ⟨C * highLowOptimizationConstant s r γ β,
    mul_pos hC (highLowOptimizationConstant_pos hs hr γ β), ?_⟩
  intro N v K hN hK hdec F G hFG
  by_cases hF : F = ∅
  · subst F
    simp only [restrictedKernelPairing_empty_left, norm_zero, zero_div, finiteSetDensity,
      card_empty, Nat.cast_zero, zero_mul, highLowEndpoint_zero hs hr, mul_zero, le_refl]
  by_cases hG : G = ∅
  · subst G
    simp only [restrictedKernelPairing_empty_right, norm_zero, zero_div, finiteSetDensity,
      card_empty, Nat.cast_zero, mul_zero, zero_div, highLowEndpoint_zero hs hr, mul_zero, le_refl]
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hF)
  have hGpos : (0 : ℝ) < G.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hG)
  have hδ : 0 < finiteSetDensity N F G := div_pos (mul_pos hFpos hGpos) (sq_pos_of_pos hN)
  have hδ1 : finiteSetDensity N F G ≤ 1 := (div_le_one (sq_pos_of_pos hN)).mpr hFG
  exact highLow_scalar_endpoint hs hr hβ hβγ hN hδ hδ1 hC.le
    (restrictedKernelPairing_crude_normalized K N v C hN hK F G)
    (fun k hk2 hkN => restrictedKernelPairing_decomposition_bound K N ((2 : ℝ) ^ k)
      s r γ β C hN (hdec k hk2 hkN) F G)

end PrimeSquares
