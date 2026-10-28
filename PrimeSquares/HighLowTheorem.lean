import PrimeSquares.OrliczOptimization
import PrimeSquares.PositivePairing

/-!
# Both restricted endpoint conclusions of Theorem 4.1

Source: t:improvinggeneral, e:endimprovbn, e:endimprovan and e:cstar.
The actual source norm inputs are collected in HighLowEndpointInputs.
Separate low, high and error constants and the fixed error power M are
retained. The error hypothesis is used only at A=1, which the source supplies.
The theorem holds for every positive real scale. Nonempty input/test sets
and |F||G|<=N^2 force N>=1; smaller scales have an empty set.
No interpolation corollary or prime-square operator input is asserted here.
-/

open Finset
open scoped lp

namespace PrimeSquares

/-- Indicator restrictions of precisely the source's local estimate,
pointwise domination and genuine lp operator norm decompositions. -/
structure HighLowEndpointInputs (KA KB : ℤ → ℂ) (windows : ℤ → Finset ℤ)
    (N v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr : ℝ) : Prop where
  nonnegative : NonnegativeKernel KB
  domination : ∀ F : Finset ℤ, ∀ x, ‖indicatorConvolution KA F x‖ ≤
    (Real.log N) ^ a * (indicatorConvolution KB F x).re
  local_bound : ∀ F : Finset ℤ, ∀ x, ‖indicatorConvolution KB F x‖ ≤
    CB * N ^ (-v) * ‖finiteIndicatorLp (F ∩ windows x) 1‖
  B_decomposition : ∀ j : ℕ, 2 ≤ (2 : ℝ) ^ j →
    (2 : ℝ) ^ j ≤ N ^ ((1 - v) / s) / 10 →
      OperatorHighLowBound KB N ((2 : ℝ) ^ j) s r γ β CB
  A_decomposition : ∀ j : ℕ, 2 ≤ (2 : ℝ) ^ j →
    Real.log ((2 : ℝ) ^ j) ≤ c₀ * (Real.log N) ^ c →
      OperatorOrliczBound KA N ((2 : ℝ) ^ j) s r α c₁ κ M 1 CLo CHi CErr

/-- Full Theorem 4.1 restricted endpoints, with every fixed coefficient
above the printed leading coefficient. Both constants are quantified before
N, the kernels, local windows, and the finite input/test sets. -/
theorem highLow_AB_endpoint {v s r γ β CB a α c₀ c₁ c κ M cstar CLo CHi CErr : ℝ}
    (hv : v < 1) (hsv : 1 - v ≤ s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hCB : 0 < CB) (ha : 0 ≤ a) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : 0 < c)
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hstar : orliczLeadingCoefficient s r c₁ κ < cstar) :
    ∃ DB : ℝ, 0 < DB ∧ ∃ DA : ℝ, 0 < DA ∧
      ∀ (N : ℝ) (KA KB : ℤ → ℂ) (windows : ℤ → Finset ℤ), 0 < N →
        HighLowEndpointInputs KA KB windows N v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr →
        ∀ F G : Finset ℤ, (F.card : ℝ) * (G.card : ℝ) ≤ N ^ 2 →
          ‖restrictedKernelPairing KB F G‖ / N ≤ DB *
            ((finiteSetDensity N F G) ^ (1 - s / (2 * (s + r))) *
              (paperLog (finiteSetDensity N F G)) ^ (γ + s * (β - γ) / (s + r))) ∧
          ‖restrictedKernelPairing KA F G‖ / N ≤ DA *
            (finiteSetDensity N F G) ^ (1 - s / (2 * (s + r))) *
              paperPhi cstar κ (finiteSetDensity N F G) := by
  have hs : 0 < s := by linarith
  let CA : ℝ := 1 + |CLo| + |CHi| + |CErr|
  have hCA : 0 < CA := by dsimp [CA]; positivity
  have hCLo : CLo ≤ CA := by dsimp [CA]; linarith [le_abs_self CLo, abs_nonneg CHi, abs_nonneg CErr]
  have hCHi : CHi ≤ CA := by dsimp [CA]; linarith [le_abs_self CHi, abs_nonneg CLo, abs_nonneg CErr]
  have hCErr : CErr ≤ CA := by dsimp [CA]; linarith [le_abs_self CErr, abs_nonneg CLo, abs_nonneg CHi]
  obtain ⟨DB, hDB, hB⟩ := highLow_B_endpoint hv hsv hr hβ hβγ hCB
  obtain ⟨DA, hDA, hscalar⟩ := orlicz_scalar_endpoint hs hr hc₁ hκ0 hκ1 hstar
    ha hc hc₀ hDB hCA α M (highLowLogExponent s r γ β)
  refine ⟨DB, hDB, DA, hDA, ?_⟩
  intro N KA KB windows hN0 H F G hFG
  have hBbound := hB N KB windows hN0 H.local_bound H.B_decomposition F G hFG
  refine ⟨hBbound, ?_⟩
  by_cases hF : F = ∅
  · subst F
    simp only [restrictedKernelPairing_empty_left, norm_zero, zero_div, finiteSetDensity,
      card_empty, Nat.cast_zero, zero_mul]
    rw [Real.zero_rpow (show 1 - s / (2 * (s + r)) ≠ 0 from
      (highLowDensityExponent_pos hs hr).ne')]
    simp only [mul_zero, zero_mul, le_refl]
  by_cases hG : G = ∅
  · subst G
    simp only [restrictedKernelPairing_empty_right, norm_zero, zero_div, finiteSetDensity,
      card_empty, Nat.cast_zero, mul_zero, zero_div]
    rw [Real.zero_rpow (show 1 - s / (2 * (s + r)) ≠ 0 from
      (highLowDensityExponent_pos hs hr).ne')]
    simp only [mul_zero, zero_mul, le_refl]
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hF)
  have hGpos : (0 : ℝ) < G.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hG)
  have hFone : (1 : ℝ) ≤ F.card := by
    exact_mod_cast Nat.succ_le_of_lt (card_pos.mpr (nonempty_iff_ne_empty.mpr hF))
  have hGone : (1 : ℝ) ≤ G.card := by
    exact_mod_cast Nat.succ_le_of_lt (card_pos.mpr (nonempty_iff_ne_empty.mpr hG))
  have hprod : (1 : ℝ) ≤ (F.card : ℝ) * (G.card : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hFone) (sub_nonneg.mpr hGone)]
  have hN : 1 ≤ N := by
    by_contra hn
    have hsmall : N < 1 := lt_of_not_ge hn
    have hp : 0 < (1 - N) * (1 + N) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hδ : 0 < finiteSetDensity N F G := div_pos (mul_pos hFpos hGpos) (sq_pos_of_pos hN0)
  have hδ1 : finiteSetDensity N F G ≤ 1 := (div_le_one (sq_pos_of_pos hN0)).mpr hFG
  have hdom := restrictedKernelPairing_domination_normalized H.nonnegative
    ((Real.log N) ^ a) N hN0 H.domination F G
  have hBscalar : ‖restrictedKernelPairing KB F G‖ / N ≤
      DB * (finiteSetDensity N F G) ^ highLowDensityExponent s r *
        (paperLog (finiteSetDensity N F G)) ^ highLowLogExponent s r γ β := by
    simpa only [highLowDensityExponent, highLowLogExponent, mul_assoc] using hBbound
  have hAdec : ∀ j : ℕ, 2 ≤ (2 : ℝ) ^ j →
      Real.log ((2 : ℝ) ^ j) ≤ c₀ * (Real.log N) ^ c →
      ‖restrictedKernelPairing KA F G‖ / N ≤
        CA * orliczScalarSum s r α c₁ κ M 1 N (finiteSetDensity N F G) ((2 : ℝ) ^ j) := by
    intro j hj hcut
    have hi := indicatorOrliczBound_of_operatorOrliczBound KA N ((2 : ℝ) ^ j)
      s r α c₁ κ M 1 CLo CHi CErr (H.A_decomposition j hj hcut)
    have hm := indicatorOrliczBound_mono KA N ((2 : ℝ) ^ j) s r α c₁ κ M 1 CLo CHi CErr CA
      hN hj hCLo hCHi hCErr hi
    exact restrictedKernelPairing_orlicz_bound KA N ((2 : ℝ) ^ j) s r α c₁ κ M 1 CA hN0 hm F G
  exact hscalar N (finiteSetDensity N F G) (‖restrictedKernelPairing KA F G‖ / N)
    (‖restrictedKernelPairing KB F G‖ / N) hN hδ hδ1 hdom hBscalar hAdec

end PrimeSquares
