import PrimeSquares.HighLowOperators
import PrimeSquares.OrliczCutoff

/-!
# Genuine three-piece operator inputs and their finite-set pairing bound

Source: Theorem 4.1, e:decompan through e:errorgeneral and e:Abalance.
The error power M and its norm constant are independent parameters. A single
positive error exponent A may be fixed; the source supplies every A>0.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def orliczHighFactor (c₁ κ Q : ℝ) : ℝ :=
  Real.exp (c₁ * (Real.log Q) ^ κ / Real.log (Real.log Q))

noncomputable def orliczScalarSum (s r α c₁ κ M A N δ Q : ℝ) : ℝ :=
  δ * Q ^ s * (Real.log Q) ^ α +
    δ ^ (1 / 2 : ℝ) * Q ^ (-r) * orliczHighFactor c₁ κ Q +
    δ ^ (1 / 2 : ℝ) * Q ^ (-r) * (Real.log Q) ^ M * (1 + Real.log N) ^ (-A)

/-- Separate source norm constants are retained in this predicate. -/
def OperatorOrliczBound (K : ℤ → ℂ) (N Q s r α c₁ κ M A CLo CHi CErr : ℝ) : Prop :=
  ∃ Lo : ℓ¹(ℤ, ℂ) → lp (fun _ : ℤ => ℂ) ⊤,
  ∃ Hi : ℓ²(ℤ, ℂ) → ℓ²(ℤ, ℂ), ∃ Err : ℓ²(ℤ, ℂ) → ℓ²(ℤ, ℂ),
    (∀ F : Finset ℤ, ∀ x, indicatorConvolution K F x =
      Lo (finiteIndicatorLp F 1) x + Hi (finiteIndicatorLp F 2) x + Err (finiteIndicatorLp F 2) x) ∧
    (∀ f : ℓ¹(ℤ, ℂ), ‖Lo f‖ ≤ CLo / N * Q ^ s * (Real.log Q) ^ α * ‖f‖) ∧
    (∀ f : ℓ²(ℤ, ℂ), ‖Hi f‖ ≤ CHi * Q ^ (-r) * orliczHighFactor c₁ κ Q * ‖f‖) ∧
    (∀ f : ℓ²(ℤ, ℂ), ‖Err f‖ ≤ CErr * Q ^ (-r) * (Real.log Q) ^ M *
      (1 + Real.log N) ^ (-A) * ‖f‖)

def IndicatorOrliczBound (K : ℤ → ℂ) (N Q s r α c₁ κ M A CLo CHi CErr : ℝ) : Prop :=
  ∀ F : Finset ℤ, ∃ lo : ℤ → ℂ, ∃ hi : ℓ²(ℤ, ℂ), ∃ err : ℓ²(ℤ, ℂ),
    (∀ x, indicatorConvolution K F x = lo x + hi x + err x) ∧
    (∀ x, ‖lo x‖ ≤ CLo / N * Q ^ s * (Real.log Q) ^ α * (F.card : ℝ)) ∧
    ‖hi‖ ≤ CHi * Q ^ (-r) * orliczHighFactor c₁ κ Q * Real.sqrt (F.card : ℝ) ∧
    ‖err‖ ≤ CErr * Q ^ (-r) * (Real.log Q) ^ M * (1 + Real.log N) ^ (-A) *
      Real.sqrt (F.card : ℝ)

theorem indicatorOrliczBound_of_operatorOrliczBound (K : ℤ → ℂ)
    (N Q s r α c₁ κ M A CLo CHi CErr : ℝ)
    (h : OperatorOrliczBound K N Q s r α c₁ κ M A CLo CHi CErr) :
    IndicatorOrliczBound K N Q s r α c₁ κ M A CLo CHi CErr := by
  obtain ⟨Lo, Hi, Err, heq, hlo, hhi, herr⟩ := h
  intro F
  refine ⟨(fun x => Lo (finiteIndicatorLp F 1) x), Hi (finiteIndicatorLp F 2),
    Err (finiteIndicatorLp F 2), heq F, ?_, ?_, ?_⟩
  · intro x
    have hb := hlo (finiteIndicatorLp F 1)
    rw [finiteIndicatorLp_one_norm] at hb
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (Lo (finiteIndicatorLp F 1)) x).trans hb
  · simpa only [finiteIndicatorLp_two_norm] using hhi (finiteIndicatorLp F 2)
  · simpa only [finiteIndicatorLp_two_norm] using herr (finiteIndicatorLp F 2)

theorem indicatorOrliczBound_mono (K : ℤ → ℂ) (N Q s r α c₁ κ M A CLo CHi CErr C : ℝ)
    (hN : 1 ≤ N) (hQ : 2 ≤ Q) (hlo : CLo ≤ C) (hhi : CHi ≤ C) (herr : CErr ≤ C)
    (h : IndicatorOrliczBound K N Q s r α c₁ κ M A CLo CHi CErr) :
    IndicatorOrliczBound K N Q s r α c₁ κ M A C C C := by
  have hQ0 : 0 ≤ Q := by linarith
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hNlog : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  intro F
  obtain ⟨lo, hi, err, heq, hl, hh, he⟩ := h F
  refine ⟨lo, hi, err, heq, ?_, ?_, ?_⟩
  · intro x
    exact (hl x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hlo (le_trans zero_le_one hN)) (Real.rpow_nonneg hQ0 _))
          (Real.rpow_nonneg hlog _)) (Nat.cast_nonneg _))
  · exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg hQ0 _))
        (Real.exp_pos _).le) (Real.sqrt_nonneg _))
  · exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right herr (Real.rpow_nonneg hQ0 _)) (Real.rpow_nonneg hlog _))
          (Real.rpow_nonneg hNlog _)) (Real.sqrt_nonneg _))

theorem finite_threePiece_pairing_bound {α : Type*} (G : Finset α) (f lo : α → ℂ)
    (hi err : ℓ²(α, ℂ)) (B : ℝ) (heq : ∀ x ∈ G, f x = lo x + hi x + err x)
    (hlo : ∀ x ∈ G, ‖lo x‖ ≤ B) :
    ‖∑ x ∈ G, f x‖ ≤ (G.card : ℝ) * B + (‖hi‖ + ‖err‖) * Real.sqrt (G.card : ℝ) := by
  have h := finite_highLow_pairing_bound G f lo (hi + err) B
    (fun x hx => by rw [heq x hx]; change lo x + hi x + err x = lo x + (hi x + err x); ring) hlo
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (norm_add_le hi err) (Real.sqrt_nonneg _)))

theorem restrictedKernelPairing_orlicz_bound (K : ℤ → ℂ)
    (N Q s r α c₁ κ M A C : ℝ) (hN : 0 < N)
    (hdec : IndicatorOrliczBound K N Q s r α c₁ κ M A C C C) (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ / N ≤
      C * orliczScalarSum s r α c₁ κ M A N (finiteSetDensity N F G) Q := by
  obtain ⟨lo, hi, err, heq, hlo, hhi, herr⟩ := hdec F
  have h := finite_threePiece_pairing_bound G (indicatorConvolution K F) lo hi err
    (C / N * Q ^ s * (Real.log Q) ^ α * (F.card : ℝ))
      (fun x _ => heq x) (fun x _ => hlo x)
  have hn := h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (add_le_add hhi herr) (Real.sqrt_nonneg _)))
  calc
    _ ≤ ((G.card : ℝ) * (C / N * Q ^ s * (Real.log Q) ^ α * (F.card : ℝ)) +
      ((C * Q ^ (-r) * orliczHighFactor c₁ κ Q * Real.sqrt (F.card : ℝ)) +
       C * Q ^ (-r) * (Real.log Q) ^ M * (1 + Real.log N) ^ (-A) * Real.sqrt (F.card : ℝ)) *
        Real.sqrt (G.card : ℝ)) / N := div_le_div_of_nonneg_right hn hN.le
    _ = _ := by
      have he := normalized_pairing_terms N (F.card : ℝ) (G.card : ℝ)
        (Q ^ s * (Real.log Q) ^ α)
        (Q ^ (-r) * orliczHighFactor c₁ κ Q + Q ^ (-r) * (Real.log Q) ^ M *
          (1 + Real.log N) ^ (-A)) C hN (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      dsimp only [orliczScalarSum, finiteSetDensity]
      convert he using 1 <;> ring

end PrimeSquares
