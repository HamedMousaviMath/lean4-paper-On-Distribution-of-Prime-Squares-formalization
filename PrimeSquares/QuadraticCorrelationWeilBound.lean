import PrimeSquares.QuadraticCorrelationZeroCorrection

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem quadraticSoftCorrelation_expansion (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) :
    quadraticSoftCorrelation p S =
      ((p : ℝ)+∑ J ∈ S.powerset.erase ∅, ∑ t : ZMod p,
        quadraticCharReal p (∏ h ∈ J, (t+h)))/(2:ℝ)^S.card := by
  unfold quadraticSoftCorrelation
  simp_rw [quadraticSoftIndicator, Finset.prod_div_distrib, Finset.prod_const]
  rw [←Finset.sum_div, quadratic_one_add_expansion]

theorem quadratic_character_expansion_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |∑ J ∈ S.powerset.erase ∅, ∑ t : ZMod p,
      quadraticCharReal p (∏ h ∈ J, (t+h))| ≤
        (2:ℝ)^S.card * (S.card : ℝ)*Real.sqrt p := by
  classical
  have hpos : 0 ≤ (S.card : ℝ)*Real.sqrt p := by positivity
  calc
    _ ≤ ∑ J ∈ S.powerset.erase ∅,
        |∑ t : ZMod p, quadraticCharReal p (∏ h ∈ J, (t+h))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _J ∈ S.powerset.erase ∅, (S.card : ℝ)*Real.sqrt p := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJS : J ⊆ S := Finset.mem_powerset.mp (Finset.mem_erase.mp hJ).2
      have hne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJ).1
      have hc : (J.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hJS
      exact (HW p hp J hne).trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
    _ = ((S.powerset.erase ∅).card : ℝ)*((S.card : ℝ)*Real.sqrt p) := by simp
    _ ≤ (2:ℝ)^S.card*((S.card : ℝ)*Real.sqrt p) := by
      apply mul_le_mul_of_nonneg_right _ hpos
      have hc : (S.powerset.erase ∅).card ≤ 2^S.card :=
        Finset.card_erase_le.trans_eq (Finset.card_powerset S)
      exact_mod_cast hc
    _ = _ := by ring

theorem quadraticSoftCorrelation_Weil_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |quadraticSoftCorrelation p S-(p:ℝ)/(2:ℝ)^S.card| ≤
      (S.card : ℝ)*Real.sqrt p := by
  have hR : (0 : ℝ)<2^S.card := by positivity
  rw [quadraticSoftCorrelation_expansion, ←sub_div, add_sub_cancel_left, abs_div,
    abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    quadratic_character_expansion_error HW p hp S

theorem quadraticCorrelation_Weil_error (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (S : Finset (ZMod p)) :
    |quadraticCorrelation p S-(p:ℝ)/(2:ℝ)^S.card| ≤
      2*(S.card : ℝ)*Real.sqrt p := by
  have hzero := quadraticSoftCorrelation_error p S
  have hhard : |quadraticCorrelation p S-quadraticSoftCorrelation p S| ≤ S.card := by
    rw [abs_sub_comm, abs_of_nonneg hzero.1]
    exact hzero.2
  have hsqrt : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Fact.out : p.Prime).one_le)
  calc
    _ ≤ |quadraticCorrelation p S-quadraticSoftCorrelation p S|+
        |quadraticSoftCorrelation p S-(p:ℝ)/(2:ℝ)^S.card| := abs_sub_le _ _ _
    _ ≤ (S.card : ℝ)+(S.card : ℝ)*Real.sqrt p :=
      add_le_add hhard (quadraticSoftCorrelation_Weil_error HW p hp S)
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) S.card]

end PrimeSquares
