import PrimeSquares.IWGoodness

set_option autoImplicit false
namespace PrimeSquares

noncomputable def realIWDenominatorBound (C : ℝ) (k : ℕ) (Q : ℝ) : ℝ :=
  C^((k:ℝ)^2*Q^(1/((k:ℝ)-1/2)))

noncomputable def realIWWidth (C : ℝ) (r k : ℕ) (Q : ℝ) : ℝ :=
  (2^20*(r:ℝ)*realIWDenominatorBound C k Q^(2*r+8))⁻¹

noncomputable def realIWMaximalCost (C : ℝ) (r k : ℕ) (Q : ℝ) : ℝ :=
  (r:ℝ)*(iwMultiplierConstant C r k)^2*
    Real.log (Real.exp 1+Q+(r:ℝ)*Real.log (realIWDenominatorBound C k Q))

theorem realIWDenominatorBound_nat (C : ℝ) (k Q : ℕ) :
    realIWDenominatorBound C k Q=iwDenominatorBound C k Q := rfl

theorem realIWWidth_nat (C : ℝ) (r k Q : ℕ) :
    realIWWidth C r k Q=iwWidth C r k Q := rfl

theorem realIWMaximalCost_nat (C : ℝ) (r k Q : ℕ) :
    realIWMaximalCost C r k Q=iwMaximalCost C r k Q := rfl

theorem realIWDenominatorBound_one_le {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q) (k : ℕ) :
    1 ≤ realIWDenominatorBound C k Q := by
  unfold realIWDenominatorBound
  exact Real.one_le_rpow (by linarith) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hQ _))

theorem realIWDenominatorBound_mono {C Q₁ Q₂ : ℝ} {k : ℕ}
    (hC : 2 ≤ C) (hk : 4 ≤ k) (hQ₁ : 0 ≤ Q₁) (hQ : Q₁ ≤ Q₂) :
    realIWDenominatorBound C k Q₁ ≤ realIWDenominatorBound C k Q₂ := by
  have hkR : (4:ℝ)≤k := by exact_mod_cast hk
  have hexp : 0 ≤ 1/((k:ℝ)-1/2) := div_nonneg (by norm_num) (by linarith)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤C)
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hQ₁ hQ hexp) (sq_nonneg _))

theorem realIWWidth_pos {C Q : ℝ} {r : ℕ}
    (hC : 2 ≤ C) (hr : 2 ≤ r) (hQ : 0 ≤ Q) (k : ℕ) :
    0 < realIWWidth C r k Q := by
  have hB := realIWDenominatorBound_one_le hC hQ k
  have hr0 : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  unfold realIWWidth
  positivity

theorem realIWWidth_antitone {C Q₁ Q₂ : ℝ} {r k : ℕ}
    (hC : 2 ≤ C) (hr : 2 ≤ r) (hk : 4 ≤ k) (hQ₁ : 0 ≤ Q₁) (hQ : Q₁ ≤ Q₂) :
    realIWWidth C r k Q₂ ≤ realIWWidth C r k Q₁ := by
  have hB := realIWDenominatorBound_one_le hC hQ₁ k
  have hBmono := realIWDenominatorBound_mono hC hk hQ₁ hQ
  have hr0 : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  unfold realIWWidth
  apply inv_anti₀ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hBmono _)
    (by positivity)

theorem iwGood_of_smaller_width {r k : ℕ} {S : Finset ℕ} {ε δ : ℝ}
    (hgood : IWGood r k S ε) (hδ : 0 < δ) (hle : δ ≤ ε) : IWGood r k S δ := by
  obtain ⟨q,hq,hs,_,hε⟩ := hgood
  exact ⟨q,hq,hs,hδ,hle.trans_lt hε⟩

theorem realIWMaximalCost_mono {C Q₁ Q₂ : ℝ} {r k : ℕ}
    (hC : 2 ≤ C) (hk : 4 ≤ k) (hQ₁ : 0 ≤ Q₁) (hQ : Q₁ ≤ Q₂) :
    realIWMaximalCost C r k Q₁ ≤ realIWMaximalCost C r k Q₂ := by
  have hB := realIWDenominatorBound_one_le hC hQ₁ k
  have hBmono := realIWDenominatorBound_mono hC hk hQ₁ hQ
  have hBlog : 0 ≤ Real.log (realIWDenominatorBound C k Q₁) := Real.log_nonneg hB
  have hlogs := Real.log_le_log (by linarith : 0<realIWDenominatorBound C k Q₁) hBmono
  unfold realIWMaximalCost
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log (by positivity)
  exact add_le_add (add_le_add le_rfl hQ) (mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg _))

end PrimeSquares
