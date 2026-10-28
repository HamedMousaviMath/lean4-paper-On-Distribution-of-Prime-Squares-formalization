import PrimeSquares.ContinuousAnnularDyadicTranslation

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def continuousAnnularSignedKernel (β : ℝ) (J : ℕ) (σ : ℕ→ℂ) (x : ℝ) : ℂ :=
  ∑ j∈range J,σ j*(Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x)-
    Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x))

theorem continuousAnnularSignedKernel_integrable (β : ℝ) (J : ℕ) (σ : ℕ→ℂ) :
    Integrable (continuousAnnularSignedKernel β J σ) volume := by
  apply integrable_finsetSum
  intro j _
  have hp := continuousAnnularKernel_complex_integrable (N := (2 : ℕ)^(j+1))
    (one_le_pow₀ (by norm_num)) β
  have hm := continuousAnnularKernel_complex_integrable (N := (2 : ℕ)^j)
    (one_le_pow₀ (by norm_num)) β
  have hd : Integrable (fun x => Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x)-
      Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x)) volume := by
    exact (hp.sub hm).congr (Filter.Eventually.of_forall (fun _ => rfl))
  exact hd.const_mul (σ j)

theorem continuousAnnularSignedKernel_shift_norm (β : ℝ) (J : ℕ) (σ : ℕ→ℂ)
    (hσ : ∀ j∈range J,‖σ j‖≤1) (h x : ℝ) :
    ‖continuousAnnularSignedKernel β J σ (x-h)-continuousAnnularSignedKernel β J σ x‖≤
      ∑ j∈range J,(|continuousAnnularKernel ((2 : ℕ)^(j+1)) β (x-h)-
        continuousAnnularKernel ((2 : ℕ)^(j+1)) β x|+
        |continuousAnnularKernel ((2 : ℕ)^j) β (x-h)-continuousAnnularKernel ((2 : ℕ)^j) β x|) := by
  have he : continuousAnnularSignedKernel β J σ (x-h)-continuousAnnularSignedKernel β J σ x=
      ∑ j∈range J,σ j*((Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β (x-h))-
        Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x))-
        (Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β (x-h))-
        Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x))) := by
    unfold continuousAnnularSignedKernel
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [he]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro j hj
  rw [norm_mul]
  calc
    _ ≤ 1*‖(Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β (x-h))-
        Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x))-
        (Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β (x-h))-
        Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x))‖ :=
      mul_le_mul_of_nonneg_right (hσ j hj) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
        norm_sub_le (Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β (x-h))-
          Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x))
          (Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β (x-h))-
          Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x))

noncomputable def farKernelTranslation (K : ℝ→ℂ) (h x : ℝ) : ℝ :=
  {y : ℝ | 2*|h| < |y|}.indicator (fun y => ‖K (y-h)-K y‖) x

theorem farKernelTranslation_integrable {K : ℝ→ℂ} (hK : Integrable K volume) (h : ℝ) :
    Integrable (farKernelTranslation K h) volume := by
  have ht : Integrable (fun x => K (x-h)) volume :=
    (measurePreserving_sub_right volume h).integrable_comp_of_integrable hK
  have hd : Integrable (fun x => ‖K (x-h)-K x‖) volume := by
    simpa only [Pi.sub_apply] using (ht.sub hK).norm
  exact hd.indicator (measurableSet_lt measurable_const continuous_abs.measurable)

theorem continuousAnnularSignedKernel_far_bound (β : ℝ) (J : ℕ) (σ : ℕ→ℂ)
    (hσ : ∀ j∈range J,‖σ j‖≤1) (h x : ℝ) :
    farKernelTranslation (continuousAnnularSignedKernel β J σ) h x≤
      ∑ j∈range J,(annularFarTranslation ((2 : ℕ)^(j+1)) β h x+
        annularFarTranslation ((2 : ℕ)^j) β h x) := by
  by_cases hx : x∈{y : ℝ | 2*|h| < |y|}
  · simp only [farKernelTranslation,annularFarTranslation,Set.indicator_of_mem hx]
    exact continuousAnnularSignedKernel_shift_norm β J σ hσ h x
  · simp only [farKernelTranslation,annularFarTranslation,Set.indicator_of_notMem hx,
      add_zero,sum_const_zero,le_refl]

end PrimeSquares
