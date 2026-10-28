import PrimeSquares.RealIWConstruction
import PrimeSquares.IWFiniteMaximumCost

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PrimeSquares

theorem iwMultiplierConstant_mono_base {C D : ℝ} (hC : 2 ≤ C) (hCD : C ≤ D)
    {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    iwMultiplierConstant C r k ≤ iwMultiplierConstant D r k := by
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hlog : (1/2:ℝ) ≤ Real.log (2+k:ℝ) :=
    real_log_two_half_le.trans (Real.log_le_log (by norm_num : (0:ℝ)<2)
      (by have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k; linarith))
  have hmul : (4:ℝ) ≤ C*(r:ℝ) := by nlinarith
  have hb : 1 ≤ C*(r:ℝ)*Real.log (2+k:ℝ) := by nlinarith
  have hbase : C*(r:ℝ)*Real.log (2+k:ℝ) ≤ D*(r:ℝ)*Real.log (2+k:ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Nat.cast_nonneg _)) (by linarith)
  unfold iwMultiplierConstant
  exact (Real.rpow_le_rpow (by linarith) hbase (by positivity)).trans
    (Real.rpow_le_rpow_of_exponent_le (hb.trans hbase)
      (mul_le_mul_of_nonneg_right hCD (Nat.cast_nonneg _)))

theorem rawIWMultiplierInput_mono_base {C D : ℝ} (hC : 2 ≤ C) (hCD : C ≤ D)
    (HIW : RawIWMultiplierInput C) : RawIWMultiplierInput D := by
  intro r k hr hk S hs hc P hP hper ε hg m hm he hmD ν hν p hp0 hp1 K hK hbound
  exact integerLpMultiplierBound_mono
    (HIW r k hr hk S hs hc P hper ε hg m hm he hmD ν hν p hp0 hp1 K hK hbound)
    (mul_le_mul_of_nonneg_right (iwMultiplierConstant_mono_base hC hCD hr k) hK)

theorem rawMajorArcSamplingInput_mono_base {C D : ℝ} (hC : 2 ≤ C) (hCD : C ≤ D)
    (HS : RawMajorArcSamplingInput C) : RawMajorArcSamplingInput D := by
  intro r k hr hk S hs hc P hP hper ε hg p hp0 hp1 u hu hdiag
  exact (HS r k hr hk S hs hc P hper ε hg p hp0 hp1 u hu hdiag).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (iwMultiplierConstant_mono_base hC hCD hr k)) _)

noncomputable def realIWAdjustedBase (C : ℝ) (k : ℕ) (Q : ℝ) : ℝ :=
  (C^2)^((Q/(⌈Q⌉₊:ℝ))^(1/((k:ℝ)-1/2)))

theorem realIWCeil_ratio_bounds {Q : ℝ} (hQ : 1 ≤ Q) :
    (0:ℝ) < (⌈Q⌉₊:ℝ) ∧ 1/2 ≤ Q/(⌈Q⌉₊:ℝ) ∧ Q/(⌈Q⌉₊:ℝ) ≤ 1 := by
  have hc : Q ≤ (⌈Q⌉₊:ℝ) := Nat.le_ceil Q
  have hc' : (⌈Q⌉₊:ℝ) < Q+1 := Nat.ceil_lt_add_one (by linarith : 0≤Q)
  have hc0 : (0:ℝ)<(⌈Q⌉₊:ℝ) := by linarith
  refine ⟨hc0, ?_, (div_le_one hc0).mpr hc⟩
  rw [le_div_iff₀ hc0]
  linarith

theorem realIWAdjusted_exponent_bounds {Q : ℝ} (hQ : 1 ≤ Q) {k : ℕ} (hk : 4 ≤ k) :
    1/2 ≤ (Q/(⌈Q⌉₊:ℝ))^(1/((k:ℝ)-1/2)) ∧
      (Q/(⌈Q⌉₊:ℝ))^(1/((k:ℝ)-1/2)) ≤ 1 := by
  have hkR : (4:ℝ)≤k := by exact_mod_cast hk
  have ha0 : 0 ≤ 1/((k:ℝ)-1/2) := div_nonneg (by norm_num) (by linarith)
  have ha1 : 1/((k:ℝ)-1/2) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  obtain ⟨_,hr0,hr1⟩ := realIWCeil_ratio_bounds hQ
  constructor
  · apply hr0.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
      (by linarith : 0<Q/(⌈Q⌉₊:ℝ)) hr1 ha1
  · exact Real.rpow_le_one (by linarith) hr1 ha0

theorem realIWAdjustedBase_bounds {C Q : ℝ} (hC : 2 ≤ C) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : 4 ≤ k) :
    C ≤ realIWAdjustedBase C k Q ∧ realIWAdjustedBase C k Q ≤ C^2 := by
  obtain ⟨ha0,ha1⟩ := realIWAdjusted_exponent_bounds hQ hk
  have hC0 : 0≤C := by linarith
  have hc : 1≤C^2 := by nlinarith
  have he : (C^2)^(1/2:ℝ)=C := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hC0]
    norm_num
  constructor
  · calc
      C = (C^2)^(1/2:ℝ) := he.symm
      _ ≤ realIWAdjustedBase C k Q := Real.rpow_le_rpow_of_exponent_le hc ha0
  · change (C^2)^_ ≤ C^2
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hc ha1

theorem realIWAdjustedBase_power (C : ℝ) {Q : ℝ} (hQ : 1 ≤ Q)
    (k : ℕ) (t : ℝ) :
    realIWAdjustedBase C k Q^(t*(⌈Q⌉₊:ℝ)^(1/((k:ℝ)-1/2))) =
      (C^2)^(t*Q^(1/((k:ℝ)-1/2))) := by
  have hc0 := (realIWCeil_ratio_bounds hQ).1
  have hp : (⌈Q⌉₊:ℝ)^(1/((k:ℝ)-1/2)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hc0 _)
  unfold realIWAdjustedBase
  rw [←Real.rpow_mul (sq_nonneg C),Real.div_rpow (by linarith : 0≤Q) hc0.le]
  congr 1
  field_simp

theorem realIWAdjustedBase_denominator (C : ℝ) {Q : ℝ} (hQ : 1 ≤ Q) (k : ℕ) :
    iwDenominatorBound (realIWAdjustedBase C k Q) k ⌈Q⌉₊ = realIWDenominatorBound (C^2) k Q := by
  exact realIWAdjustedBase_power C hQ k ((k:ℝ)^2)

theorem realIWAdjustedBase_width (C : ℝ) {Q : ℝ} (hQ : 1 ≤ Q) (r k : ℕ) :
    iwWidth (realIWAdjustedBase C k Q) r k ⌈Q⌉₊ = realIWWidth (C^2) r k Q := by
  unfold iwWidth realIWWidth
  rw [realIWAdjustedBase_denominator C hQ]

end PrimeSquares
