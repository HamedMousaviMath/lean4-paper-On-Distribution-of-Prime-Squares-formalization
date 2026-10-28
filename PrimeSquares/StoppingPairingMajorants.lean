import PrimeSquares.Proposition419
import PrimeSquares.OrliczPairing

/-!
# Finite pairings at genuinely varying arithmetic scales

The high output is controlled by the actual real l2 supremum supplied by
Proposition 4.19. A fixed-scale operator norm is not substituted for it.
-/

open Finset
open scoped lp
namespace PrimeSquares

theorem finite_pairing_real_l2_majorant {α : Type*} (G : Finset α)
    (u : α → ℂ) (H : ℓ²(α, ℝ)) (hH : ∀ x ∈ G, ‖u x‖ ≤ H x) :
    ‖∑ x ∈ G, u x‖ ≤ ‖H‖ * Real.sqrt (G.card : ℝ) := by
  apply norm_finite_sum_le_energy G u ‖H‖ (norm_nonneg _)
  calc
    _ ≤ ∑ x ∈ G, ‖H x‖^2 := sum_le_sum (fun x hx => pow_le_pow_left₀ (norm_nonneg _)
      ((hH x hx).trans (le_abs_self (H x))) 2)
    _ ≤ _ := by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) H G

theorem finite_threePiece_majorant_bound {α : Type*} (G : Finset α)
    (u lo hi err : α → ℂ) (H E : ℓ²(α, ℝ)) (B : ℝ)
    (heq : ∀ x ∈ G, u x = lo x + hi x + err x)
    (hlo : ∀ x ∈ G, ‖lo x‖ ≤ B)
    (hhi : ∀ x ∈ G, ‖hi x‖ ≤ H x) (herr : ∀ x ∈ G, ‖err x‖ ≤ E x) :
    ‖∑ x ∈ G, u x‖ ≤ (G.card : ℝ)*B + (‖H‖+‖E‖)*Real.sqrt (G.card : ℝ) := by
  have hs : (∑ x ∈ G, u x) = (∑ x ∈ G, lo x) + (∑ x ∈ G, hi x) + ∑ x ∈ G, err x := by
    simp only [← sum_add_distrib]
    exact sum_congr rfl heq
  rw [hs]
  calc
    _ ≤ ‖∑ x ∈ G, lo x‖ + ‖∑ x ∈ G, hi x‖ + ‖∑ x ∈ G, err x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (G.card : ℝ)*B + ‖H‖*Real.sqrt (G.card : ℝ) + ‖E‖*Real.sqrt (G.card : ℝ) :=
      add_le_add (add_le_add (norm_finite_sum_le_card_mul G lo B hlo)
        (finite_pairing_real_l2_majorant G hi H hhi)) (finite_pairing_real_l2_majorant G err E herr)
    _ = _ := by ring

theorem selectedPrimeHigh_stopping_pairing {c δ ε Q N₀ : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ)
    (hε : 0 < ε) (hQ : 2 ≤ Q) (hN₀ : 2 ≤ N₀)
    (hcut : Real.log Q ≤ δ * Real.sqrt (Real.log N₀)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F G : Finset ℤ) (τ : ℤ → ℕ),
      (∀ x ∈ G, N₀ ≤ (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ)) →
      ‖∑ x ∈ G, selectedPrimeHigh D ((2 : ℕ)^(τ x)*2)
        (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x); omega)
        Q (finiteIndicatorLp F 2) x‖ ≤
        (K * Q^(-(1/2 : ℝ)) * Real.exp ((2+ε)*regularizedHighExponentWeight Q)) *
          Real.sqrt (F.card : ℝ) * Real.sqrt (G.card : ℝ) := by
  obtain ⟨K, hK, _, hmax⟩ := H419.high ε hε
  refine ⟨K, hK, ?_⟩
  intro F G τ hτ
  obtain ⟨H, _, _, hmajor, hnorm, _⟩ := hmax Q N₀ hQ hN₀ hcut (finiteIndicatorLp F 2)
  have hm : ∀ x ∈ G, ‖selectedPrimeHigh D ((2 : ℕ)^(τ x)*2)
      (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x); omega)
      Q (finiteIndicatorLp F 2) x‖ ≤ H x := by
    intro x hx
    have ht := hmajor (τ x) x
    rw [selectedPrimeHighTail_of_le D N₀ Q (τ x) (hτ x hx)] at ht
    exact ht
  exact (finite_pairing_real_l2_majorant G _ H hm).trans
    (by simpa only [finiteIndicatorLp_two_norm] using
      mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg (G.card : ℝ)))

theorem selectedPrimeLow_stopping_pairing {c δ Q B : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ)
    (hQ : 2 ≤ Q) (F G : Finset ℤ) (τ : ℤ → ℕ)
    (hcut : ∀ x ∈ G, Real.log Q ≤ δ * Real.sqrt (Real.log (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ)))
    (hτ : ∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤ B) :
    ‖∑ x ∈ G, selectedPrimeLow D ((2 : ℕ)^(τ x)*2)
      (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x); omega)
      Q (finiteIndicatorLp F 1) x‖ ≤
      (G.card : ℝ) * (8*lowSpatialConstant*Q*Real.log (2*Q)*B) := by
  apply norm_finite_sum_le_card_mul
  intro x hx
  have hn : (2 : ℕ) ≤ (2 : ℕ)^(τ x)*2 := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x)
  exact (H419.low_local _ hn Q hQ (hcut x hx) _ (finiteIndicatorLp F 1) x).trans
    (mul_le_mul_of_nonneg_left (hτ x hx) (by
      have := lowSpatialConstant_nonneg
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2*Q by linarith)
      positivity))

end PrimeSquares
