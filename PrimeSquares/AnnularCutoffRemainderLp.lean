import PrimeSquares.AnnularCutoffRemainderBounds
import PrimeSquares.RieszThorinMultiplierInterface

set_option autoImplicit false
namespace PrimeSquares

noncomputable def annularRemainderConstant : ℝ := 1+2*cutoffL1Constant+4/Real.pi

theorem annularRemainderConstant_pos : 0< annularRemainderConstant := by
  have h := cutoffL1Constant_nonneg
  unfold annularRemainderConstant
  positivity

theorem annularRemainderConstant_bounds :
    2*cutoffL1Constant≤ annularRemainderConstant ∧ 4/Real.pi≤ annularRemainderConstant := by
  have h := cutoffL1Constant_nonneg
  have hp : 0<(4 : ℝ)/Real.pi := by positivity
  unfold annularRemainderConstant
  constructor <;> linarith

theorem annularCutoffRemainder_Lp (HY : RawYoungMultiplierInput) (HRT : RawRieszThorinMultiplierInput)
    {N r : ℕ} (hN : 2≤ N) (hr : 2≤ r) {β a b : ℝ} (hβ0 : 0<β) (hβ1 : β≤1)
    (ha : 0< a) (hb : 0< b) (hab : 2*a≤ b) :
    RealLpMultiplierBound (ENNReal.ofReal (iwNearOneExponent r))
      (annularCutoffRemainderSymbol N (by omega) β hβ0.le hβ1 a b)
      (annularRemainderConstant*(b/(N : ℝ)^2)^((r : ℝ)⁻¹)) := by
  have hNp : (0 : ℝ)< N := by exact_mod_cast (show 0< N by omega)
  have hA := annularRemainderConstant_pos
  have hc := annularRemainderConstant_bounds
  have h1 := realLpMultiplierBound_mono
    (annularCutoffRemainder_Lp_rough HY (by omega : 1≤ N) hβ0 hβ1 ha hb (by norm_num : (1 : ℝ)≤1)) hc.1
  rw [ENNReal.ofReal_one] at h1
  have h2 := annularCutoffRemainder_L2 hN hβ0.le hβ1 ha.le hb hab
  have htwo : 4*b/(Real.pi*(N : ℝ)^2)≤ annularRemainderConstant*(b/(N : ℝ)^2) := by
    have h := mul_le_mul_of_nonneg_right hc.2 (div_nonneg hb.le (sq_nonneg (N : ℝ)))
    exact (by convert h using 1; ring)
  have hint := real_interpolate_one_two_at_iw HRT _ hr hA
    (by positivity : 0< annularRemainderConstant*(b/(N : ℝ)^2)) h1
    (realLpMultiplierBound_mono h2 htwo)
  have he : annularRemainderConstant^(1-(r : ℝ)⁻¹)*
      (annularRemainderConstant*(b/(N : ℝ)^2))^((r : ℝ)⁻¹)=
      annularRemainderConstant*(b/(N : ℝ)^2)^((r : ℝ)⁻¹) := by
    rw [Real.mul_rpow hA.le (div_nonneg hb.le (sq_nonneg (N : ℝ))),←mul_assoc,
      ←Real.rpow_add hA,sub_add_cancel,Real.rpow_one]
  rwa [he] at hint

end PrimeSquares
