import PrimeSquares.IWTransitionScale

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwRemainderRatio (r : ℕ) : ℝ := Real.exp (-(r : ℝ)⁻¹)

theorem iwRemainderRatio_bounds {r : ℕ} (hr : 2 ≤ r) :
    0 < iwRemainderRatio r ∧ iwRemainderRatio r < 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos (inv_pos.mpr hrR))⟩

theorem iwRemainderRatio_sum_bound {r : ℕ} (hr : 2 ≤ r) :
    ∑' j : ℕ, iwRemainderRatio r ^ j ≤ 2 * (r : ℝ) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hx : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hrp
  have hx2 : (r : ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using (inv_le_inv₀ hrp (by norm_num : (0 : ℝ) < 2)).mpr hrR
  have hq := iwRemainderRatio_bounds hr
  have hhalf : (1/2 : ℝ) ≤ iwRemainderRatio r := by
    have h := Real.add_one_le_exp (-(r : ℝ)⁻¹)
    change 1/2 ≤ Real.exp (-(r : ℝ)⁻¹)
    linarith
  have he : iwRemainderRatio r * Real.exp ((r : ℝ)⁻¹) = 1 := by
    rw [iwRemainderRatio, ←Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((r : ℝ)⁻¹)) hq.1.le
  rw [he] at hm
  have hsmall : (r : ℝ)⁻¹/2 ≤ 1-iwRemainderRatio r := by
    nlinarith
  rw [tsum_geometric_of_lt_one hq.1.le hq.2]
  apply (inv_le_iff_one_le_mul₀ (sub_pos.mpr hq.2)).mpr
  have hmul := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 2*(r : ℝ) by positivity)
  have hid : (r : ℝ)⁻¹/2*(2*(r : ℝ)) = 1 := by field_simp
  linarith

theorem iwNarrow_inverse_geometry {C : ℝ} (hC : 2 ≤ C) {r k Q P : ℕ}
    (hr : 2 ≤ r) (hP : 1 ≤ P) :
    0 < (iwNarrowWidth (iwWidth C r k Q) P)⁻¹ ∧
      2 * iwCutoffScale C r k Q ≤ (iwNarrowWidth (iwWidth C r k Q) P)⁻¹ ∧
      2 ≤ (iwNarrowWidth (iwWidth C r k Q) P)⁻¹ := by
  have hw := iwWidth_pos hC hr k Q
  have hd := iwNarrowWidth_pos hw hP
  have hb := iwNarrowWidth_le_original (iwWidth C r k Q) P
  have hh : iwNarrowWidth (iwWidth C r k Q) P ≤ iwWidth C r k Q / 2 := by linarith
  have hi := (inv_le_inv₀ (by positivity : 0 < iwWidth C r k Q / 2) hd).mpr hh
  have hcore : 2 * iwCutoffScale C r k Q ≤ (iwNarrowWidth (iwWidth C r k Q) P)⁻¹ := by
    simpa only [iwCutoffScale, div_eq_mul_inv, mul_inv_rev, inv_inv] using hi
  have ha := iwCutoffScale_four_le hC hr k Q
  exact ⟨inv_pos.mpr hd, hcore, by linarith⟩

theorem iwTransitionScale_two_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/100) :
    2 ≤ iwTransitionScale δ := by
  have hs := (iwTransitionScale_squared_bounds hδ0 (by linarith)).1
  by_contra hn
  have hsmall : (iwTransitionScale δ : ℝ) ≤ 1 := by exact_mod_cast (show iwTransitionScale δ ≤ 1 by omega)
  have hn0 := Nat.cast_nonneg (α := ℝ) (iwTransitionScale δ)
  have hsq : (iwTransitionScale δ : ℝ)^2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq hδ0.le
  nlinarith

theorem iw_transition_remainder_decay {r : ℕ} (hr : 2 ≤ r)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (j : ℕ) :
    (δ⁻¹ / (((2 : ℕ)^j * iwTransitionScale δ : ℕ) : ℝ)^2)^((r : ℝ)⁻¹) ≤
      iwRemainderRatio r ^ j := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hm : (0 : ℝ) < iwTransitionScale δ := by dsimp [iwTransitionScale]; positivity
  have htwo : (0 : ℝ) < ((2 : ℕ)^j : ℕ) := by exact_mod_cast (show (0 : ℕ) < 2^j by positivity)
  have hs := (iwTransitionScale_squared_bounds hδ0 hδ1).1
  have hb : δ⁻¹ / (((2 : ℕ)^j * iwTransitionScale δ : ℕ) : ℝ)^2 ≤ ((4 : ℝ)^j)⁻¹ := by
    apply (div_le_iff₀ (by push_cast; positivity : (0 : ℝ) < (((2 : ℕ)^j * iwTransitionScale δ : ℕ) : ℝ)^2)).mpr
    have hd : δ⁻¹ ≤ (iwTransitionScale δ : ℝ)^2 := by
      apply (inv_le_iff_one_le_mul₀ hδ0).mpr
      nlinarith
    calc
      δ⁻¹ ≤ (iwTransitionScale δ : ℝ)^2 := hd
      _ = ((4 : ℝ)^j)⁻¹ * (((2 : ℕ)^j * iwTransitionScale δ : ℕ) : ℝ)^2 := by
        push_cast
        rw [mul_pow, ←pow_mul, show (2 : ℝ)^(j*2) = 4^j by rw [mul_comm j 2, pow_mul]; norm_num,
          ←mul_assoc, inv_mul_cancel₀ (by positivity : (4 : ℝ)^j ≠ 0), one_mul]
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ δ⁻¹ / (((2 : ℕ)^j * iwTransitionScale δ : ℕ) : ℝ)^2)
    hb (inv_nonneg.mpr hrp.le)
  apply hp.trans
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < ((4 : ℝ)^j)⁻¹),
    Real.log_inv, Real.log_pow, iwRemainderRatio, ←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hl4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := real_log_two_half_le
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hp0 : 0 ≤ (j : ℝ) * (r : ℝ)⁻¹ := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hl4) hp0]

end PrimeSquares
