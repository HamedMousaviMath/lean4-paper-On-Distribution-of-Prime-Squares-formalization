import PrimeSquares.CutoffGeometricSeries

open Finset
namespace PrimeSquares

theorem cutoff_power_divide {Q : ℝ} (hQ : 0 < Q) (δ : ℝ) : Q^(1-δ)/Q=Q^(-δ) := by
  rw [Real.rpow_sub hQ]
  simp only [Real.rpow_one,Real.rpow_neg hQ.le]
  field_simp

noncomputable def collarPowerConstant (C δ : ℝ) : ℝ :=
  (192*C/Real.pi)*((2 : ℝ)^(1-δ)/((2 : ℝ)^(1-δ)-1))

theorem collarPowerConstant_pos {C δ : ℝ} (hC : 0 < C) (hδ : δ < 1) :
    0 < collarPowerConstant C δ := by
  have hh := collar_dyadic_ratio_gt_one hδ
  unfold collarPowerConstant
  positivity

theorem collar_block_constant_sum {Q C δ : ℝ} (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hδ : δ < 1) :
    (∑ s ∈ range (Nat.log2 ⌊Q⌋₊+1),(192*C/(Real.pi*Q))*((2 : ℝ)^(1-δ))^s) ≤
      collarPowerConstant C δ*Q^(-δ) := by
  rw [←mul_sum]
  have hQp : 0 < Q := by linarith
  have hpi := Real.pi_pos
  have hnonneg : 0 ≤ 192*C/(Real.pi*Q) := by positivity
  have hh := mul_le_mul_of_nonneg_left (cutoff_growing_series hQ hδ) hnonneg
  calc
    _ ≤ _ := hh
    _ = collarPowerConstant C δ*(Q^(1-δ)/Q) := by unfold collarPowerConstant;ring
    _ = _ := by rw [cutoff_power_divide (by linarith : 0 < Q)]

end PrimeSquares
