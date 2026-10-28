import PrimeSquares.StoppingPairingMajorants
import PrimeSquares.LocalPrimeScalarBalance

/-! # Normalize the actual three-piece varying-scale pairing -/

open Finset
open scoped lp
namespace PrimeSquares

theorem normalizedStoppingPairing (F G H : Finset ℤ) (hGH : G ⊆ H)
    (u lo hi err : ℤ → ℂ) (Hi Er : ℓ²(ℤ, ℝ)) {L C Q c₁ : ℝ}
    (hL : 0 < L) (hC : 0 ≤ C) (hQ : 2 ≤ Q)
    (heq : ∀ x ∈ G, u x = lo x + hi x + err x)
    (hlo : ∀ x ∈ G, ‖lo x‖ ≤ C/L*Q*Real.log Q*(F.card : ℝ))
    (hhi : ∀ x ∈ G, ‖hi x‖ ≤ Hi x) (herr : ∀ x ∈ G, ‖err x‖ ≤ Er x)
    (hHinorm : ‖Hi‖ ≤ C*Q^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) Q*Real.sqrt (F.card : ℝ))
    (hErnorm : ‖Er‖ ≤ C*Q^(-(1/2 : ℝ))*Real.sqrt (F.card : ℝ)) :
    ‖∑ x ∈ G, u x‖/L ≤ C*localPrimeScalar c₁ (finiteSetDensity L F H) Q := by
  have hQ0 : 0 < Q := by linarith
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hcard : (G.card : ℝ) ≤ H.card := by exact_mod_cast card_le_card hGH
  have hLow0 : 0 ≤ C/L*Q*Real.log Q*(F.card : ℝ) := by positivity
  have hraw := finite_threePiece_majorant_bound G u lo hi err Hi Er _ heq hlo hhi herr
  have hs : ‖Hi‖ + ‖Er‖ ≤ C*Q^(-(1/2 : ℝ))*
      (orliczHighFactor c₁ (1/2) Q+1)*Real.sqrt (F.card : ℝ) := by
    exact (add_le_add hHinorm hErnorm).trans_eq (by ring)
  have hs0 : 0 ≤ C*Q^(-(1/2 : ℝ))*
      (orliczHighFactor c₁ (1/2) Q+1)*Real.sqrt (F.card : ℝ) := by
    have hh := (Real.exp_pos (c₁*(Real.log Q)^(1/2 : ℝ)/Real.log (Real.log Q))).le
    change 0 ≤ C*Q^(-(1/2 : ℝ))*(Real.exp _+1)*Real.sqrt (F.card : ℝ)
    positivity
  have hbig : ‖∑ x ∈ G, u x‖ ≤
      (H.card : ℝ)*(C/L*Q*Real.log Q*(F.card : ℝ)) +
      (C*Q^(-(1/2 : ℝ))*(orliczHighFactor c₁ (1/2) Q+1)*Real.sqrt (F.card : ℝ))*
        Real.sqrt (H.card : ℝ) := hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcard hLow0)
    (mul_le_mul hs (Real.sqrt_le_sqrt hcard) (Real.sqrt_nonneg _) hs0))
  have he := normalized_pairing_terms L (F.card : ℝ) (H.card : ℝ) (Q*Real.log Q)
    (Q^(-(1/2 : ℝ))*(orliczHighFactor c₁ (1/2) Q+1)) C hL
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ((H.card : ℝ)*(C/L*Q*Real.log Q*(F.card : ℝ)) +
      (C*Q^(-(1/2 : ℝ))*(orliczHighFactor c₁ (1/2) Q+1)*Real.sqrt (F.card : ℝ))*
        Real.sqrt (H.card : ℝ))/L := div_le_div_of_nonneg_right hbig hL.le
    _ = _ := by
      dsimp only [finiteSetDensity, localPrimeScalar]
      convert he using 1 <;> ring

end PrimeSquares
