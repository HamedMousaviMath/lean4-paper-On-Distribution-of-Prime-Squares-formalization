import PrimeSquares.GoldbachWeightedMeanValue

set_option autoImplicit false
namespace PrimeSquares

theorem goldbach_weighted_log_offset (a u : ℝ) (ha : 2≤a) (hau : a≤u) :
    1/Real.sqrt (Real.log u)≤
      Real.sqrt (1+Real.log 2/Real.log a)/Real.sqrt (Real.log (2*u)) := by
  have ha0 : 0<a := by linarith
  have hu0 : 0<u := by linarith
  have hloga : 0<Real.log a := Real.log_pos (by linarith)
  have hlogu : 0<Real.log u := Real.log_pos (by linarith)
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hmon := Real.log_le_log ha0 hau
  have hC : 0≤1+Real.log 2/Real.log a := by positivity
  have hineq : Real.log 2+Real.log u≤(1+Real.log 2/Real.log a)*Real.log u := by
    apply (mul_le_mul_iff_left₀ hloga).mp
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hmon hlog2]
  have hlogsum : Real.log (2*u)=Real.log 2+Real.log u :=
    Real.log_mul (by norm_num) hu0.ne'
  rw [←hlogsum] at hineq
  have hs := Real.sqrt_le_sqrt hineq
  rw [Real.sqrt_mul hC] at hs
  have hlog2u : 0<Real.log (2*u) := by rw [hlogsum];linarith
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hlogu) (Real.sqrt_pos.mpr hlog2u)).mpr
  simpa only [one_mul] using hs

theorem goldbach_weighted_log_loss (T m ℓ L₀ η : ℝ) (hT : 0<T) (hm : 0<m)
    (hℓ : 0<ℓ) (hL₀ : 0<L₀) (hη0 : 0≤η) (hη1 : η<1)
    (hfloor : L₀≤Real.log (T/ℓ)) (hloss : Real.log (T/m)≤η*L₀) :
    0<Real.log (m/ℓ) ∧
      1/(Real.log (m/ℓ))^2≤(1/(1-η)^2)*(1/(Real.log (T/ℓ))^2) := by
  have hid : Real.log (m/ℓ)=Real.log (T/ℓ)-Real.log (T/m) := by
    rw [Real.log_div hm.ne' hℓ.ne',Real.log_div hT.ne' hℓ.ne',Real.log_div hT.ne' hm.ne']
    ring
  have hlogT : 0<Real.log (T/ℓ) := hL₀.trans_le hfloor
  have hbound : (1-η)*Real.log (T/ℓ)≤Real.log (m/ℓ) := by
    rw [hid]
    have hh := hloss.trans (mul_le_mul_of_nonneg_left hfloor hη0)
    linarith
  have hpos : 0<(1-η)*Real.log (T/ℓ) := mul_pos (by linarith) hlogT
  refine ⟨hpos.trans_le hbound,?_⟩
  have hh := one_div_le_one_div_of_le (sq_pos_of_pos hpos)
    (pow_le_pow_left₀ hpos.le hbound 2)
  apply hh.trans_eq
  rw [mul_pow]
  simp only [one_div,mul_inv_rev]
  ring

noncomputable def goldbachWeightedUpperConstant (α : ℝ) : ℝ :=
  16*Real.exp (-Real.eulerMascheroniConstant/2)/Real.sqrt (Real.pi*α)

theorem goldbach_weighted_upper_constant_positive (α : ℝ) (hα : 0<α) :
    0<goldbachWeightedUpperConstant α := by
  unfold goldbachWeightedUpperConstant
  exact div_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hα))

theorem goldbach_weighted_upper_constant_normalization (α : ℝ) (hα : 0<α) :
    3*Real.sqrt α*goldbachWeightedUpperConstant α=48*goldbachHalfMeanConstant := by
  have hsα := (Real.sqrt_pos.mpr hα).ne'
  have hsπ := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold goldbachWeightedUpperConstant goldbachHalfMeanConstant
  rw [Real.sqrt_mul Real.pi_pos.le]
  field_simp
  norm_num

end PrimeSquares
