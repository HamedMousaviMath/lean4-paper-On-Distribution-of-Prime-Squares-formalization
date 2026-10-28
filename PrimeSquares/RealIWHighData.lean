import PrimeSquares.RealIWSourceLow

set_option autoImplicit false
namespace PrimeSquares

noncomputable def realIWUpperBase (C : ℝ) (k : ℕ) (Q : ℝ) : ℝ :=
  C^((Q/(⌊Q⌋₊:ℝ))^(1/((k:ℝ)-1/2)))

theorem realIWFloor_bounds {Q : ℝ} (hQ : 2 ≤ Q) :
    (1:ℝ) ≤ (⌊Q⌋₊:ℝ) ∧ Q/2 ≤ (⌊Q⌋₊:ℝ) ∧ (⌊Q⌋₊:ℝ) ≤ Q := by
  have hn : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by norm_num; linarith : ((1:ℕ):ℝ)≤Q)
  have hnR : (1:ℝ)≤(⌊Q⌋₊:ℝ) := by exact_mod_cast hn
  have hlt : Q < (⌊Q⌋₊:ℝ)+1 := Nat.lt_floor_add_one Q
  exact ⟨hnR,by linarith,Nat.floor_le (by linarith : 0≤Q)⟩

theorem realIWUpperBase_lower {C Q : ℝ} (hC : 2 ≤ C) (hQ : 2 ≤ Q)
    {k : ℕ} (hk : 4 ≤ k) : C ≤ realIWUpperBase C k Q := by
  have hf := realIWFloor_bounds hQ
  have hr : 1 ≤ Q/(⌊Q⌋₊:ℝ) := (one_le_div (by linarith : (0:ℝ)<(⌊Q⌋₊:ℝ))).mpr hf.2.2
  have hkR : (4:ℝ)≤k := by exact_mod_cast hk
  have ha : 0 ≤ 1/((k:ℝ)-1/2) := div_nonneg (by norm_num) (by linarith)
  have he : 1 ≤ (Q/(⌊Q⌋₊:ℝ))^(1/((k:ℝ)-1/2)) := Real.one_le_rpow hr ha
  unfold realIWUpperBase
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤C) he

theorem realIWUpperBase_power {C : ℝ} (hC : 0 ≤ C) {Q : ℝ} (hQ : 2 ≤ Q) (k : ℕ) (t : ℝ) :
    realIWUpperBase C k Q^(t*(⌊Q⌋₊:ℝ)^(1/((k:ℝ)-1/2))) =
      C^(t*Q^(1/((k:ℝ)-1/2))) := by
  have hf0 : (0:ℝ)<(⌊Q⌋₊:ℝ) := by linarith [(realIWFloor_bounds hQ).1]
  have hp : (⌊Q⌋₊:ℝ)^(1/((k:ℝ)-1/2)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hf0 _)
  unfold realIWUpperBase
  rw [←Real.rpow_mul hC,Real.div_rpow (by linarith : 0≤Q) hf0.le]
  congr 1
  field_simp

theorem realIWUpperBase_denominator {C Q : ℝ} (hC : 0 ≤ C) (hQ : 2 ≤ Q) (k : ℕ) :
    iwDenominatorBound (realIWUpperBase C k Q) k ⌊Q⌋₊ = realIWDenominatorBound C k Q :=
  realIWUpperBase_power hC hQ k ((k:ℝ)^2)

theorem realIWUpperBase_cutoff {C Q : ℝ} (hC : 0 ≤ C) (hQ : 2 ≤ Q) (r k : ℕ) :
    iwCutoffScale (realIWUpperBase C k Q) r k ⌊Q⌋₊ = realIWCutoffScale C r k Q := by
  unfold iwCutoffScale iwWidth realIWCutoffScale realIWWidth
  rw [realIWUpperBase_denominator hC hQ]

noncomputable def realIWHighData {C Q : ℝ} (hC : 2 ≤ C) (hQ : 2 ≤ Q)
    {k : ℕ} (hk : 4 ≤ k) (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) :
    TaoArcConstructionData (realIWUpperBase C k Q) (iwRho k) k ⌊Q⌋₊ where
  S := d.S
  positive := d.positive
  coprime := d.coprime
  period := d.period
  period_pos := d.period_pos
  period_bound := d.period_bound
  covered := d.covered
  periodic := d.periodic
  component_bound := by
    intro s hs
    rw [iwRho_half hk,realIWUpperBase_power (by linarith : 0≤C) hQ]
    apply (d.component_bound s hs).trans
    rw [iwRho_half hk]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤C)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (realIWFloor_bounds hQ).2.2
          (by have hkR : (4:ℝ)≤k := by exact_mod_cast hk
              exact div_nonneg (by norm_num) (by linarith))) (Nat.cast_nonneg k))

theorem realIWFloor_quarter_power {Q : ℝ} (hQ : 2 ≤ Q) :
    (⌊Q⌋₊:ℝ)^(-(1/4:ℝ)) ≤ 2*Q^(-(1/4:ℝ)) := by
  have hf := realIWFloor_bounds hQ
  have hQ0 : 0<Q := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos (by linarith : 0<Q/2) hf.2.1 (by norm_num : -(1/4:ℝ)≤0)
  have htwo : (2:ℝ)^(1/4:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (1/4:ℝ)≤1)
  calc
    _ ≤ (Q/2)^(-(1/4:ℝ)) := hpow
    _ = Q^(-(1/4:ℝ))*(2:ℝ)^(1/4:ℝ) := by
      rw [Real.div_rpow hQ0.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
      simp only [div_eq_mul_inv,inv_inv]
    _ ≤ _ := (mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hQ0.le _)).trans_eq (mul_comm _ _)

end PrimeSquares

