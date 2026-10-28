import PrimeSquares.GoldbachSingularSmoothing

set_option autoImplicit false
open MeasureTheory FourierTransform
namespace PrimeSquares

theorem goldbach_affine_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ→E) {a : ℝ} (ha : 0<a) (b : ℝ) :
    (∫ x : ℝ,g x)=a • ∫ v : ℝ,g (a*v+b) := by
  have hi := Measure.integral_comp_mul_left (fun x : ℝ=>g (x+b)) a
  rw [integral_add_right_eq_self] at hi
  rw [hi,abs_of_pos (inv_pos.mpr ha),smul_smul,mul_inv_cancel₀ ha.ne',one_smul]

theorem goldbach_forward_fourier_integral (g : ℝ→ℂ) (γ : ℝ) :
    𝓕 g γ=∫ x : ℝ,realFourierPhase (-γ*x)*g x := by
  have h := real_inverse_fourier_integral g (-γ)
  rw [Real.fourierInv_eq_fourier_neg,neg_neg] at h
  simpa only [mul_neg,neg_mul,mul_comm] using h

noncomputable def goldbachQuadraticAverage (μ : Measure ℝ) (f g : ℝ→ℂ) (a x : ℝ) : ℂ :=
  (a:ℂ)⁻¹*∫ u : ℝ,f u*g ((x-u^2)/a) ∂μ

theorem goldbach_quadratic_density_joint (μ : Measure ℝ) [SFinite μ]
    (f g : ℝ→ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g) {a : ℝ} (ha : 0<a) :
    Integrable (fun p : ℝ×ℝ=>f p.1*g ((p.2-p.1^2)/a)) (μ.prod volume) := by
  have hsm : StronglyMeasurable (fun p : ℝ×ℝ=>f p.1*g ((p.2-p.1^2)/a)) :=
    ((hfm.comp measurable_fst).mul (hgm.comp ((measurable_snd.sub (measurable_fst.pow_const 2)).div_const a))).stronglyMeasurable
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun u=>((hg.comp_div ha.ne').comp_sub_right (u^2)).const_mul (f u)),?_⟩
  have he (u : ℝ) : (∫ x : ℝ,‖f u*g ((x-u^2)/a)‖)=‖f u‖*(a*∫ v : ℝ,‖g v‖) := by
    simp only [norm_mul]
    rw [integral_const_mul,integral_sub_right_eq_self (fun x : ℝ=>‖g (x/a)‖) (u^2),
      Measure.integral_comp_div (fun x : ℝ=>‖g x‖) a,abs_of_pos ha,smul_eq_mul]
  simp only [he]
  exact hf.norm.mul_const _

theorem goldbach_quadratic_average_integrable (μ : Measure ℝ) [SFinite μ]
    (f g : ℝ→ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g) {a : ℝ} (ha : 0<a) :
    Integrable (goldbachQuadraticAverage μ f g a) :=
  (goldbach_quadratic_density_joint μ f g hfm hgm hf hg ha).integral_prod_right.const_mul _

theorem goldbach_quadratic_average_fourier (μ : Measure ℝ) [SFinite μ]
    (f g : ℝ→ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g) {a : ℝ} (ha : 0<a) (γ : ℝ) :
    𝓕 (goldbachQuadraticAverage μ f g a) γ=
      (∫ u : ℝ,realFourierPhase (-γ*u^2)*f u ∂μ)*
      ∫ v : ℝ,realFourierPhase ((-a*γ)*v)*g v := by
  let F := fun p : ℝ×ℝ=>realFourierPhase (-γ*p.2)*(f p.1*g ((p.2-p.1^2)/a))
  have hJ := goldbach_quadratic_density_joint μ f g hfm hgm hf hg ha
  have hmeas : Measurable F :=
    (realFourierPhase_continuous.measurable.comp (measurable_const.mul measurable_snd)).mul
      ((hfm.comp measurable_fst).mul (hgm.comp ((measurable_snd.sub (measurable_fst.pow_const 2)).div_const a)))
  have hi : Integrable F (μ.prod volume) := hJ.norm.mono' hmeas.aestronglyMeasurable (by
    filter_upwards with p
    simp only [F,norm_mul,realFourierPhase_norm,one_mul]
    exact le_rfl)
  have hinner (u : ℝ) : (∫ x : ℝ,F (u,x))=
      (a:ℂ)*(realFourierPhase (-γ*u^2)*f u)*
        ∫ v : ℝ,realFourierPhase ((-a*γ)*v)*g v := by
    rw [goldbach_affine_integral (fun x : ℝ=>F (u,x)) ha (u^2)]
    have he (v : ℝ) : F (u,a*v+u^2)=
        (realFourierPhase (-γ*u^2)*f u)*(realFourierPhase ((-a*γ)*v)*g v) := by
      have hx : (a*v+u^2-u^2)/a=v := by field_simp;ring
      dsimp only [F]
      rw [hx,show -γ*(a*v+u^2)=(-γ*u^2)+((-a*γ)*v) by ring,realFourierPhase_add]
      ring
    simp only [he,integral_const_mul,Complex.real_smul]
    ring
  rw [goldbach_forward_fourier_integral]
  have he : (∫ x : ℝ,realFourierPhase (-γ*x)*goldbachQuadraticAverage μ f g a x)=
      (a:ℂ)⁻¹*(∫ x : ℝ,(∫ u : ℝ,F (u,x) ∂μ)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    unfold goldbachQuadraticAverage
    rw [←integral_const_mul,←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    dsimp only [F]
    ring
  rw [he,←integral_integral_swap hi]
  simp_rw [hinner,integral_mul_const,integral_const_mul]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne']

end PrimeSquares
