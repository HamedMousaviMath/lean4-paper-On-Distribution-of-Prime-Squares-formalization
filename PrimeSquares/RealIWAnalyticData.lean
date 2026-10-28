import PrimeSquares.RealIWBase
import PrimeSquares.AnalyticIWLow

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PrimeSquares

theorem realIWAdjusted_cost {C Q : ℝ} (hC : 2 ≤ C) (hQ : 1 ≤ Q)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k) :
    iwMaximalCost (realIWAdjustedBase C k Q) r k ⌈Q⌉₊ ≤
      2*realIWMaximalCost (C^2) r k Q := by
  have hCC : 2≤C^2 := by nlinarith
  have hbounds := realIWAdjustedBase_bounds hC hQ hk
  have hA : 2≤realIWAdjustedBase C k Q := hC.trans hbounds.1
  have hmult := iwMultiplierConstant_mono_base hA hbounds.2 hr k
  have hmult0 := iwMultiplierConstant_nonneg (by linarith : 0≤realIWAdjustedBase C k Q) r k
  have hB := realIWDenominatorBound_one_le hCC (by linarith : 0≤Q) k
  have hBlog := Real.log_nonneg hB
  let X := Real.exp 1+Q+(r:ℝ)*Real.log (realIWDenominatorBound (C^2) k Q)
  have he : (1:ℝ)≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have hX : 2≤X := by
    dsimp [X]
    nlinarith [mul_nonneg (Nat.cast_nonneg r) hBlog]
  have hceil : (⌈Q⌉₊:ℝ) ≤ Q+1 := (Nat.ceil_lt_add_one (by linarith : 0≤Q)).le
  have hY : 0<Real.exp 1+(⌈Q⌉₊:ℝ)+(r:ℝ)*Real.log (realIWDenominatorBound (C^2) k Q) := by
    have hc : (0:ℝ)≤(⌈Q⌉₊:ℝ) := Nat.cast_nonneg _
    nlinarith [Real.exp_pos (1:ℝ),mul_nonneg (Nat.cast_nonneg r) hBlog]
  have hlog : Real.log (Real.exp 1+(⌈Q⌉₊:ℝ)+(r:ℝ)*Real.log (realIWDenominatorBound (C^2) k Q)) ≤
      2*Real.log X := by
    calc
      _ ≤ Real.log (X^2) := Real.log_le_log hY (by dsimp [X]; nlinarith [sq_nonneg (X-1)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hfac : (r:ℝ)*(iwMultiplierConstant (realIWAdjustedBase C k Q) r k)^2 ≤
      (r:ℝ)*(iwMultiplierConstant (C^2) r k)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmult0 hmult 2) (Nat.cast_nonneg r)
  unfold iwMaximalCost realIWMaximalCost
  rw [realIWAdjustedBase_denominator C hQ]
  calc
    _ ≤ ((r:ℝ)*(iwMultiplierConstant (realIWAdjustedBase C k Q) r k)^2)*(2*Real.log X) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ ((r:ℝ)*(iwMultiplierConstant (C^2) r k)^2)*(2*Real.log X) :=
      mul_le_mul_of_nonneg_right hfac (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
    _ = _ := by dsimp [X]; ring

noncomputable def realIWAnalyticData {C Q : ℝ} (hC : 2 ≤ C) (hQ : 1 ≤ Q)
    {k : ℕ} (hk : 4 ≤ k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) :
    AnalyticTaoArcData (realIWAdjustedBase C k Q) (iwRho k) k ⌈Q⌉₊ where
  S := d.S
  positive := d.positive
  coprime := d.coprime
  period := d.period
  period_pos := d.period_pos
  period_bound := d.period_bound.trans (Nat.pow_le_pow_right (by norm_num) (Nat.floor_le_ceil Q))
  periodic := d.periodic
  component_bound := by
    intro s hs
    rw [iwRho_half hk,realIWAdjustedBase_power C hQ]
    apply (d.component_bound s hs).trans
    rw [iwRho_half hk]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith : 1≤C^2)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith : 0≤Q))
          (by have hkR : (4:ℝ)≤k := by exact_mod_cast hk
              exact div_nonneg (by norm_num) (by linarith))) (Nat.cast_nonneg k))

theorem realIWAnalyticData_width {C Q : ℝ} (hC : 2 ≤ C) (hQ : 1 ≤ Q)
    {r k : ℕ} (hk : 4 ≤ k)
    (d : TaoArcConstructionData (C^2) (iwRho k) k ⌊Q⌋₊) :
    iwWidth (realIWAdjustedBase C k Q) r k ⌈Q⌉₊ = realIWWidth (C^2) r k Q ∧
      (realIWAnalyticData hC hQ hk d).S=d.S ∧ (realIWAnalyticData hC hQ hk d).period=d.period :=
  ⟨realIWAdjustedBase_width C hQ r k,rfl,rfl⟩

end PrimeSquares
