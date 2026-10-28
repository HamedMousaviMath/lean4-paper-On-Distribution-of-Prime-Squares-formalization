import PrimeSquares.ContinuousAnnularConvolution

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def realAnnularKernelDensity (N β x : ℝ) : ℝ := x^(β/2-1)/(2*N)
noncomputable def realContinuousAnnularKernel (N β : ℝ) : ℝ → ℝ :=
  (Set.Icc (N^2/4) (N^2)).indicator (realAnnularKernelDensity N β)
noncomputable def realContinuousAnnularConvolution (N β : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  convolution (fun y => Complex.ofReal (realContinuousAnnularKernel N β y)) f
    (ContinuousLinearMap.mul ℂ ℂ) volume

theorem realContinuousAnnularKernel_nat (N : ℕ) (β : ℝ) :
    realContinuousAnnularKernel (N:ℝ) β=continuousAnnularKernel N β := rfl

theorem realAnnularKernelDensity_continuousOn {N : ℝ} (hN : 0 < N) (β : ℝ) :
    ContinuousOn (realAnnularKernelDensity N β) (Set.Icc (N^2/4) (N^2)) := by
  intro x hx
  have hxp : 0 < x := (by positivity : (0:ℝ)<N^2/4).trans_le hx.1
  exact ((Real.continuousAt_rpow_const x (β/2-1) (Or.inl hxp.ne')).div_const _).continuousWithinAt

theorem realContinuousAnnularKernel_integrable {N : ℝ} (hN : 0 < N) (β : ℝ) :
    Integrable (realContinuousAnnularKernel N β) volume :=
  (realAnnularKernelDensity_continuousOn hN β).integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem realContinuousAnnularKernel_complex_integrable {N : ℝ} (hN : 0 < N) (β : ℝ) :
    Integrable (fun x => Complex.ofReal (realContinuousAnnularKernel N β x)) volume := by
  have hc := Complex.continuous_ofReal.comp_continuousOn (realAnnularKernelDensity_continuousOn hN β)
  have hi : Integrable ((Set.Icc (N^2/4) (N^2)).indicator
      (fun x : ℝ => Complex.ofReal (realAnnularKernelDensity N β x))) volume :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  convert hi using 1
  funext x
  by_cases hx : x∈Set.Icc (N^2/4) (N^2)
  · simp only [realContinuousAnnularKernel,Set.indicator_of_mem hx]
  · simp only [realContinuousAnnularKernel,Set.indicator_of_notMem hx,Complex.ofReal_zero]

theorem realContinuousAnnularKernel_nonneg {N : ℝ} (hN : 0 < N) (β x : ℝ) :
    0 ≤ realContinuousAnnularKernel N β x := by
  by_cases hx : x∈Set.Icc (N^2/4) (N^2)
  · rw [realContinuousAnnularKernel,Set.indicator_of_mem hx]
    exact div_nonneg (Real.rpow_nonneg ((by positivity : (0:ℝ)≤N^2/4).trans hx.1) _)
      (by positivity)
  · rw [realContinuousAnnularKernel,Set.indicator_of_notMem hx]

theorem realAnnularKernelDensity_bound {N β x : ℝ} (hN : 2 ≤ N) (hβ : β ≤ 1)
    (hx : x∈Set.Icc (N^2/4) (N^2)) : realAnnularKernelDensity N β x ≤ 1/N^2 := by
  have hNp : 0 < N := by linarith
  have hx1 : 1 ≤ x := by nlinarith [hx.1]
  have hxp : 0 < x := by linarith
  have hsqrt : N/2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith [hx.1])
  have hpow : x^(β/2-1) ≤ 1/Real.sqrt x := by
    calc
      _ ≤ x^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = _ := by rw [Real.rpow_neg hxp.le,←Real.sqrt_eq_rpow,one_div]
  have hinv : 1/Real.sqrt x ≤ 2/N := by
    have h := one_div_le_one_div_of_le (by positivity : (0:ℝ)<N/2) hsqrt
    exact h.trans_eq (by ring)
  unfold realAnnularKernelDensity
  apply (div_le_iff₀ (show 0 < 2*N by positivity)).mpr
  exact (hpow.trans hinv).trans_eq (by field_simp)

theorem realContinuousAnnularKernel_box_bound {N β : ℝ} (hN : 2 ≤ N) (hβ : β ≤ 1) (x : ℝ) :
    realContinuousAnnularKernel N β x ≤ if 0 ≤ x ∧ x ≤ N^2 then 1/N^2 else 0 := by
  have hNp : 0 < N := by linarith
  by_cases hx : x∈Set.Icc (N^2/4) (N^2)
  · have hb : 0 ≤ x ∧ x ≤ N^2 := ⟨(by positivity : (0:ℝ)≤N^2/4).trans hx.1,hx.2⟩
    rw [realContinuousAnnularKernel,Set.indicator_of_mem hx,ite_eq_left hb]
    exact realAnnularKernelDensity_bound hN hβ hx
  · rw [realContinuousAnnularKernel,Set.indicator_of_notMem hx]
    split_ifs <;> positivity

end PrimeSquares
