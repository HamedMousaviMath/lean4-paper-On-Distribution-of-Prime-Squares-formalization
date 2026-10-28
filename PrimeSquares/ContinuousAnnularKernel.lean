import PrimeSquares.ContinuousAnnularSignedL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
open MeasureTheory
open scoped Classical
namespace PrimeSquares

noncomputable def annularKernelDensity (N : ℕ) (β x : ℝ) : ℝ :=
  x^(β/2-1)/(2*(N : ℝ))

/-- The literal real annular density in the source. Closed endpoints make no
difference to its Lebesgue measure or convolution. -/
noncomputable def continuousAnnularKernel (N : ℕ) (β : ℝ) : ℝ → ℝ :=
  (Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)).indicator (annularKernelDensity N β)

theorem continuousAnnularKernel_of_mem {N : ℕ} {β x : ℝ}
    (hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) :
    continuousAnnularKernel N β x=annularKernelDensity N β x :=
  Set.indicator_of_mem hx _

theorem continuousAnnularKernel_of_not_mem {N : ℕ} {β x : ℝ}
    (hx : x∉Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) : continuousAnnularKernel N β x=0 :=
  Set.indicator_of_notMem hx _

theorem annularKernelDensity_continuousOn {N : ℕ} (hN : 1≤N) (β : ℝ) :
    ContinuousOn (annularKernelDensity N β) (Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) := by
  intro x hx
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hxp : 0<x := (by positivity : (0 : ℝ)<(N : ℝ)^2/4).trans_le hx.1
  exact ((Real.continuousAt_rpow_const x (β/2-1) (Or.inl hxp.ne')).div_const _).continuousWithinAt

theorem continuousAnnularKernel_integrable {N : ℕ} (hN : 1≤N) (β : ℝ) :
    Integrable (continuousAnnularKernel N β) volume :=
  (annularKernelDensity_continuousOn hN β).integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem continuousAnnularKernel_complex_integrable {N : ℕ} (hN : 1≤N) (β : ℝ) :
    Integrable (fun x => Complex.ofReal (continuousAnnularKernel N β x)) volume := by
  have hc := Complex.continuous_ofReal.comp_continuousOn (annularKernelDensity_continuousOn hN β)
  have hi : Integrable ((Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)).indicator
      (fun x : ℝ => Complex.ofReal (annularKernelDensity N β x))) volume :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  convert hi using 1
  funext x
  by_cases hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)
  · simp only [continuousAnnularKernel,Set.indicator_of_mem hx]
  · simp only [continuousAnnularKernel,Set.indicator_of_notMem hx,Complex.ofReal_zero]

theorem continuousAnnularKernel_nonneg {N : ℕ} (hN : 1≤N) (β x : ℝ) :
    0≤continuousAnnularKernel N β x := by
  by_cases hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)
  · rw [continuousAnnularKernel_of_mem hx]
    exact div_nonneg (Real.rpow_nonneg ((by positivity : (0 : ℝ)≤(N : ℝ)^2/4).trans hx.1) _)
      (by positivity)
  · rw [continuousAnnularKernel_of_not_mem hx]

theorem annularKernelDensity_bound {N : ℕ} (hN : 2≤N) {β x : ℝ} (hβ1 : β≤1)
    (hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)) :
    annularKernelDensity N β x≤1/(N : ℝ)^2 := by
  have hNr : (2 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hx1 : 1≤x := by nlinarith [hx.1]
  have hxp : 0<x := by linarith
  have hsqrt : (N : ℝ)/2≤Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith [hx.1])
  have hpow : x^(β/2-1)≤1/Real.sqrt x := by
    calc
      _ ≤ x^(-(1/2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = _ := by rw [Real.rpow_neg hxp.le,←Real.sqrt_eq_rpow,one_div]
  have hinv : 1/Real.sqrt x≤2/(N : ℝ) := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<(N : ℝ)/2) hsqrt
    exact h.trans_eq (by ring)
  unfold annularKernelDensity
  apply (div_le_iff₀ (show 0<2*(N : ℝ) by positivity)).mpr
  exact (hpow.trans hinv).trans_eq (by field_simp)

theorem continuousAnnularKernel_box_bound {N : ℕ} (hN : 2≤N) {β : ℝ} (hβ1 : β≤1) (x : ℝ) :
    continuousAnnularKernel N β x≤ if 0≤x ∧ x≤(N : ℝ)^2 then 1/(N : ℝ)^2 else 0 := by
  by_cases hx : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2)
  · have hbox : 0≤x ∧ x≤(N : ℝ)^2 :=
      ⟨(by positivity : (0 : ℝ)≤(N : ℝ)^2/4).trans hx.1,hx.2⟩
    rw [continuousAnnularKernel_of_mem hx,ite_eq_left hbox]
    exact annularKernelDensity_bound hN hβ1 hx
  · rw [continuousAnnularKernel_of_not_mem hx]
    split_ifs <;> positivity

end PrimeSquares
