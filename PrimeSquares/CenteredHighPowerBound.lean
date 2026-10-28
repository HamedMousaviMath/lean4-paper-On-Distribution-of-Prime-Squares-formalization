import PrimeSquares.MaskedGaussPairBounds
import PrimeSquares.GeneralGaussDecay

namespace PrimeSquares

theorem centeredHighSymbol_power_bound {N : ℕ} (hN : 2 ≤ N) (q₀ : ℕ) [NeZero q₀]
    {Q C T δ η : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hratio : conductorMajorant q₀/(q₀ : ℝ) ≤ T) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hG : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q),IsUnit a →
      ‖principalSquareSum q a‖ ≤ C*(q : ℝ)^(-δ) ∧ ‖twistedSquareSum q χ a‖ ≤ C*(q : ℝ)^(-δ))
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (r : ℚ) (hk : ‖κ r‖ ≤ 1) (θ : ℝ) :
    ‖centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀) χ κ β r θ‖ ≤
      (2*C*highMaskConstant*(1+T))*Q^(-η)*(r.den : ℝ)^(-(δ-η)) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hq₀ : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  obtain ⟨hp,ht⟩ := hG r.den (χ r) (r.num : ZMod r.den) ha
  have hh := maskedGaussPair_two_bounds hN hβ0 hβ1 hq hq₀ hQ hB hC hT hratio
    (principalSquareSum r.den (r.num : ZMod r.den)) (twistedSquareSum r.den (χ r) (r.num : ZMod r.den)) (κ r) hp ht hk θ
  rw [centeredHighSymbol_mask_formula N (by omega) q₀ (NeZero.pos q₀) hQ hB χ κ β r θ]
  have hbroad : ‖Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,sourceArcCutoffScale,abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact sourceArcCutoff_le_one _
  have hm : ‖(principalSquareSum r.den (r.num : ZMod r.den)*annularHighFactor N 1 (r.den : ℝ) Q θ-
      twistedSquareSum r.den (χ r) (r.num : ZMod r.den)*(κ r*annularHighFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/conductorMajorant q₀) θ))*
      Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ)‖ ≤
      ‖principalSquareSum r.den (r.num : ZMod r.den)*annularHighFactor N 1 (r.den : ℝ) Q θ-
        twistedSquareSum r.den (χ r) (r.num : ZMod r.den)*(κ r*annularHighFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/conductorMajorant q₀) θ)‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hbroad (norm_nonneg _)).trans (by simp)
  have hK : 0 < highMaskConstant := (by norm_num : (0 : ℝ) < 1).trans_le highMaskConstant_one_le
  have hD : 0 ≤ 2*C*highMaskConstant*(1+T) := by positivity
  exact two_bounds_rpow_interpolate hD hq hQ hη0 hη1 (hm.trans hh.1) (hm.trans hh.2)

end PrimeSquares
