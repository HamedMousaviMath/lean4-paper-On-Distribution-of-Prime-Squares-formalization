import PrimeSquares.NearOneQuantitativeGrowth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Set MeasureTheory
namespace PrimeSquares

noncomputable def nearOnePowerConstant (C a e : ℝ) : ℝ :=
  (1+Real.exp 1/a)*Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e))

theorem nearOnePowerConstant_pos {a : ℝ} (ha : 0<a) (C e : ℝ) :
    0<nearOnePowerConstant C a e := by unfold nearOnePowerConstant;positivity

theorem nearOnePsi_power_majorant {C a e u : ℝ} (hC : 1≤C) (ha : 0<a)
    (he : 0<e) (he1 : e≤1) (hu : a≤u) :
    nearOnePsi C u≤nearOnePowerConstant C a e*u^(1+e/2) := by
  have hu0 : 0<u := ha.trans_le hu
  have h1 := nearOnePsi_le_density (show 0≤C by linarith) hu0.le
  have h2 := nearOneDensity_small_power hC he he1 (t := u)
  rw [max_eq_right hu0.le] at h2
  have hbase : Real.exp 1+u≤(1+Real.exp 1/a)*u := by
    have h := mul_le_mul_of_nonneg_left hu (div_nonneg (Real.exp_pos 1).le ha.le)
    have heq : (Real.exp 1/a)*a=Real.exp 1 := by field_simp
    rw [heq] at h
    nlinarith
  have hpow : (Real.exp 1+u)^(e/2)≤(1+Real.exp 1/a)*u^(e/2) := by
    calc
      _ ≤ ((1+Real.exp 1/a)*u)^(e/2) := Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = (1+Real.exp 1/a)^(e/2)*u^(e/2) := Real.mul_rpow (by positivity) hu0.le
      _ ≤ (1+Real.exp 1/a)^1*u^(e/2) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by have := div_nonneg (Real.exp_pos (1 : ℝ)).le ha.le;linarith : 1≤1+Real.exp 1/a)
          (by linarith : e/2≤1)) (by positivity)
      _ = _ := by rw [Real.rpow_one]
  have h3 := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e))).le
  have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hu0.le
  have heq : u*((Real.exp (nearOneGrowthConstant C/e*Real.log (Real.exp 1/e)))*
      ((1+Real.exp 1/a)*u^(e/2)))=nearOnePowerConstant C a e*u^(1+e/2) := by
    rw [Real.rpow_add hu0,Real.rpow_one]
    unfold nearOnePowerConstant
    ring
  exact h1.trans (h4.trans_eq heq)

theorem nearOneGaugeMoment_majorant {C a e u : ℝ} (hC : 1≤C) (ha : 0<a)
    (he : 0<e) (he1 : e≤1) (hu : a≤u) :
    nearOnePsi C u*u^(-e-2)≤nearOnePowerConstant C a e*u^(-1-e/2) := by
  have hu0 : 0<u := ha.trans_le hu
  calc
    _ ≤ (nearOnePowerConstant C a e*u^(1+e/2))*u^(-e-2) :=
      mul_le_mul_of_nonneg_right (nearOnePsi_power_majorant hC ha he he1 hu) (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hu0];congr 2;ring

theorem nearOneGaugeMoment_integrable {C a e : ℝ} (hC : 1≤C) (ha : 0<a)
    (he : 0<e) (he1 : e≤1) :
    IntegrableOn (fun u : ℝ => nearOnePsi C u*u^(-e-2)) (Ioi a) := by
  have hg := (integrableOn_Ioi_rpow_of_lt (show -1-e/2 < -1 by linarith) ha).const_mul
    (nearOnePowerConstant C a e)
  have hc : ContinuousOn (fun u : ℝ => nearOnePsi C u*u^(-e-2)) (Ioi a) := by
    intro u hu
    exact (nearOnePsi_continuous C).continuousAt.continuousWithinAt.mul
      (Real.continuousAt_rpow_const u (-e-2) (Or.inl (ne_of_gt (ha.trans hu)))).continuousWithinAt
  apply hg.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0<u := ha.trans hu
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (nearOnePsi_nonneg C hu0.le) (Real.rpow_nonneg hu0.le _))]
  exact nearOneGaugeMoment_majorant hC ha he he1 hu.le

theorem nearOneGaugeMoment_bound {C a e : ℝ} (hC : 1≤C) (ha : 0<a)
    (he : 0<e) (he1 : e≤1) :
    (∫ u : ℝ in Ioi a,nearOnePsi C u*u^(-e-2))≤
      nearOnePowerConstant C a e*(2/e)*a^(-e/2) := by
  have hf := nearOneGaugeMoment_integrable hC ha he he1
  have hg := (integrableOn_Ioi_rpow_of_lt (show -1-e/2 < -1 by linarith) ha).const_mul
    (nearOnePowerConstant C a e)
  have h := setIntegral_mono_on hf hg measurableSet_Ioi
    (fun u hu => nearOneGaugeMoment_majorant hC ha he he1 hu.le)
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (show -1-e/2 < -1 by linarith) ha] at h
  have heq : nearOnePowerConstant C a e*(-a^((-1-e/2)+1)/((-1-e/2)+1))=
      nearOnePowerConstant C a e*(2/e)*a^(-e/2) := by
    rw [show (-1-e/2)+1=-e/2 by ring]
    field_simp
  exact h.trans_eq heq

end PrimeSquares
