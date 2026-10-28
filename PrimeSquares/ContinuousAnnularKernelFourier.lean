import PrimeSquares.ContinuousAnnularKernel
import PrimeSquares.RealInverseFourierIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem annularKernelDensity_substitution {N : ℕ} (β : ℝ) {t : ℝ} (ht : 0<t) :
    (2*t)*annularKernelDensity N β (t^2)=(N : ℝ)⁻¹*t^(β-1) := by
  have hp : (t^2)^(β/2-1)=t^(β-2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ht.le]
    congr 1
    ring
  have hm : t*t^(β-2)=t^(β-1) := by
    calc
      _ = t^(1 : ℝ)*t^(β-2) := by rw [Real.rpow_one]
      _ = t^((1 : ℝ)+(β-2)) := (Real.rpow_add ht _ _).symm
      _ = _ := by congr 1;ring
  unfold annularKernelDensity
  rw [hp]
  calc
    _ = (N : ℝ)⁻¹*(t*t^(β-2)) := by ring
    _ = _ := by rw [hm]

/-- The literal kernel has exactly the Fourier multiplier used throughout the
paper. The substitution t -> t^2, its derivative and endpoints are checked. -/
theorem continuousAnnularKernel_fourier {N : ℕ} (hN : 1≤N) (β θ : ℝ) :
    𝓕 (fun x => Complex.ofReal (continuousAnnularKernel N β x)) θ=
      annularOscillatoryModel N β θ := by
  let a := (N : ℝ)^2/4
  let b := (N : ℝ)^2
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := by dsimp [a];positivity
  have hab : a≤b := by dsimp [a,b];nlinarith [sq_nonneg (N : ℝ)]
  let phase := fun x : ℝ => Complex.exp (Complex.ofReal (-2*Real.pi*x*θ)*Complex.I)
  let g := fun x : ℝ => phase x*Complex.ofReal (annularKernelDensity N β (max x a))
  have hg : Continuous g := by
    apply Continuous.mul
    · dsimp [phase]
      fun_prop
    · apply Complex.continuous_ofReal.comp
      unfold annularKernelDensity
      apply Continuous.div_const
      apply Continuous.rpow_const
      · exact continuous_id.max continuous_const
      · intro x
        exact Or.inl (ne_of_gt (ha.trans_le (le_max_right x a)))
  have hc := intervalIntegral.integral_deriv_smul_comp (a := (N : ℝ)/2) (b := (N : ℝ))
    (f := fun t : ℝ => t^2) (f' := fun t : ℝ => 2*t) (g := g)
    (fun t _ => by simpa using hasDerivAt_pow 2 t) (by fun_prop) hg
  have hendpoint : ((N : ℝ)/2)^2=a := by dsimp [a];ring
  simp only [Function.comp_apply,hendpoint] at hc
  have hsub : ∀ t∈Set.uIcc ((N : ℝ)/2) N,(2*t) • g (t^2)=
      Complex.ofReal ((N : ℝ)⁻¹)*
        (Complex.ofReal (t^(β-1))*quadraticOscillation θ t) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (N : ℝ)/2≤N)] at ht
    have ht0 : 0<t := (by positivity : (0 : ℝ)<(N : ℝ)/2).trans_le ht.1
    have hta : a≤t^2 := by dsimp [a];nlinarith [ht.1]
    have hphase : phase (t^2)=quadraticOscillation θ t := by
      dsimp [phase,quadraticOscillation]
      congr 1
      push_cast
      ring
    change Complex.ofReal (2*t)*(phase (t^2)*Complex.ofReal (annularKernelDensity N β (max (t^2) a)))=_
    rw [max_eq_left hta,hphase]
    calc
      _ = Complex.ofReal ((2*t)*annularKernelDensity N β (t^2))*quadraticOscillation θ t := by
        rw [Complex.ofReal_mul]
        push_cast
        ring
      _ = _ := by rw [annularKernelDensity_substitution (N := N) β ht0,Complex.ofReal_mul];ring
  have hFT : 𝓕 (fun x => Complex.ofReal (continuousAnnularKernel N β x)) θ=
      ∫ x in a..b,g x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have he : (fun x : ℝ => Complex.exp (Complex.ofReal (-2*Real.pi*x*θ)*Complex.I) •
        Complex.ofReal (continuousAnnularKernel N β x))=
        (Set.Icc a b).indicator (fun x => phase x*Complex.ofReal (annularKernelDensity N β x)) := by
      funext x
      by_cases hx : x∈Set.Icc a b
      · have hx' : x∈Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2) := hx
        rw [continuousAnnularKernel_of_mem hx',Set.indicator_of_mem hx]
        rfl
      · have hx' : x∉Set.Icc ((N : ℝ)^2/4) ((N : ℝ)^2) := hx
        rw [continuousAnnularKernel_of_not_mem hx',Set.indicator_of_notMem hx,Complex.ofReal_zero,smul_zero]
    rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    dsimp [g]
    rw [max_eq_left hx.1]
  rw [hFT,←hc]
  calc
    _ = ∫ t in (N : ℝ)/2..N,Complex.ofReal ((N : ℝ)⁻¹)*
        (Complex.ofReal (t^(β-1))*quadraticOscillation θ t) := intervalIntegral.integral_congr hsub
    _ = _ := by rw [intervalIntegral.integral_const_mul,annularOscillatoryModel_interval]

end PrimeSquares
