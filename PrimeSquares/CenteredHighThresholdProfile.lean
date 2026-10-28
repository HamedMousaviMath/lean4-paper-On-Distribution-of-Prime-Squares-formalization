import PrimeSquares.ThresholdMaskedCoefficientBounds
import PrimeSquares.InducedRationalCoefficientBudget
import PrimeSquares.CenteredHighMaskFormula

namespace PrimeSquares

theorem principal_rationalGauss_rho_bound (r : ℚ) :
    ‖rationalPrincipalGauss r‖ ≤ 4*(r.den : ℝ)^(-(1/2 : ℝ))*conductorRho r.den := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  have h := (principalSquareSum_finite_product_bound r.den (r.num : ZMod r.den) ha).trans
    (mul_le_mul_of_nonneg_left (gaussOddProduct_le_conductorRho r.den) (by positivity))
  rw [Real.rpow_neg (Nat.cast_nonneg r.den),←Real.sqrt_eq_rpow]
  simpa only [rationalPrincipalGauss,div_eq_mul_inv] using h

theorem centeredHighSymbol_threshold_profile {N : ℕ} (hN : 2 ≤ N)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    (active : Bool) {Q S β : ℝ} (hQ : 0 < Q) (hS : 0 ≤ S)
    (hσ : conductorSigma q₀ χ₀*(conductorMajorant q₀)^(1/2 : ℝ) ≤ S)
    (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : ℚ) (θ : ℝ) :
    ‖centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β r θ‖ ≤
      (4*highMaskConstant*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)))*
        relativeCutoffProfile (1/4) ((r.den : ℝ)/Q)+
      (32*highMaskConstant*S*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)))*
        relativeCutoffProfile (1/4) ((r.den : ℝ)/(Q*(q₀ : ℝ)/conductorMajorant q₀)) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hq₀ : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  have hB := conductorMajorant_one_le q₀ (NeZero.pos q₀)
  have hBp : 0 < conductorMajorant q₀ := by linarith
  have hK : 0 ≤ highMaskConstant := (by norm_num : (0 : ℝ) ≤ 1).trans highMaskConstant_one_le
  have hhalf : (1/2 : ℝ) ≤ highMaskConstant := by linarith [highMaskConstant_one_le]
  have hp := threshold_masked_product r.den r.den_pos (B := 1) (A := 4) (by norm_num)
    hQ (by norm_num) hK hL hSlope (rationalPrincipalGauss r)
    (annularHighFactor N 1 (r.den : ℝ) Q θ) (principal_rationalGauss_rho_bound r)
    ((annularHighFactor_half hN (by norm_num) _ _ _).trans hhalf)
    (by simpa only [mul_one,mul_div_assoc] using (annularHighFactor_linear hN
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) hq hQ θ))
  simp only [Real.one_rpow,mul_one] at hp
  have ht : ‖rationalTwistedGauss r (sourceInducedCharacter q₀ χ₀ r)*
      (sourceExceptionalSelector q₀ active r*annularHighFactor N β (r.den : ℝ)
        (Q*(q₀ : ℝ)/conductorMajorant q₀) θ)‖ ≤
      (32*highMaskConstant*S*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q)))*
        relativeCutoffProfile (1/4) ((r.den : ℝ)/(Q*(q₀ : ℝ)/conductorMajorant q₀)) := by
    by_cases hdiv : q₀ ∣ r.den
    · let d : ℕ := r.den/q₀
      have hden : q₀*d=r.den := Nat.mul_div_cancel' hdiv
      have hd : 0 < d := by
        have hn : d ≠ 0 := by
          intro hz
          have he : r.den=0 := by rw [←hden,hz,mul_zero]
          exact r.den_pos.ne' he
        exact Nat.pos_of_ne_zero hn
      have hid : (r.den : ℝ)/(Q*(q₀ : ℝ)/conductorMajorant q₀)=
          (d : ℝ)*conductorMajorant q₀/Q := by
        have hh : (q₀ : ℝ)*(d : ℝ)=(r.den : ℝ) := by exact_mod_cast hden
        rw [←hh]
        field_simp
      have hc : ‖rationalTwistedGauss r (sourceInducedCharacter q₀ χ₀ r)*sourceExceptionalSelector q₀ active r‖ ≤
          (32*conductorSigma q₀ χ₀)*(d : ℝ)^(-(1/2 : ℝ))*conductorRho d := by
        rw [norm_mul]
        exact ((mul_le_mul_of_nonneg_left (sourceExceptionalSelector_norm q₀ active r)
          (norm_nonneg _)).trans_eq (mul_one _)).trans
          (sourceInduced_rationalGauss_div_bound q₀ χ₀ hχ r hdiv)
      have hs := threshold_masked_product d hd hB hQ
        (mul_nonneg (by norm_num) (conductorSigma_nonneg _ _)) hK hL hSlope
        (rationalTwistedGauss r (sourceInducedCharacter q₀ χ₀ r)*sourceExceptionalSelector q₀ active r)
        (annularHighFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/conductorMajorant q₀) θ) hc
        ((annularHighFactor_half hN hβ1 _ _ _).trans hhalf)
        (by simpa only [←hid,mul_div_assoc] using (annularHighFactor_linear hN hβ0 hβ1 hq
          (div_pos (mul_pos hQ hq₀) hBp) θ))
      rw [mul_assoc] at hs
      rw [hid]
      have hprof : 0 ≤ relativeCutoffProfile (1/4) ((d : ℝ)*conductorMajorant q₀/Q) :=
        relativeCutoffProfile_nonneg (by positivity)
      calc
        _ ≤ _ := hs
        _ = (32*highMaskConstant*Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q))*
            relativeCutoffProfile (1/4) ((d : ℝ)*conductorMajorant q₀/Q))*
            (conductorSigma q₀ χ₀*(conductorMajorant q₀)^(1/2 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hσ (by positivity)
        _ = _ := by ring
    · have hz : sourceExceptionalSelector q₀ active r=0 := by
        simp only [sourceExceptionalSelector,hdiv,and_false,ite_false]
      rw [hz,zero_mul,mul_zero,norm_zero]
      exact mul_nonneg (by positivity) (relativeCutoffProfile_nonneg (by positivity))
  rw [centeredHighSymbol_mask_formula N (by omega) q₀ (NeZero.pos q₀) hQ hBp]
  have hbroad : ‖Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,sourceArcCutoffScale,abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact sourceArcCutoff_le_one _
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_left hbroad (norm_nonneg _)).trans_eq (mul_one _)).trans
    ((norm_sub_le _ _).trans (add_le_add hp ht))

end PrimeSquares
